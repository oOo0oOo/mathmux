#!/usr/bin/env python3
"""Measure repeated switching among dirty module-system files."""

from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path
import random
import statistics
import threading
from typing import Any, Callable

import experiment as base


STRATEGIES = [
    "lsp-keep-open",
    "lsp-close-on-switch",
    "lean-cached-setup",
    "lean-setup-each",
    "cli-snapshot",
    "lake-build",
]


def measure_call(action: Callable[[], Any], pid: int) -> tuple[Any, float, float]:
    stop = threading.Event()
    peak_kib = 0

    def sample() -> None:
        nonlocal peak_kib
        while not stop.is_set():
            peak_kib = max(peak_kib, base.process_tree_rss_kib(pid))
            stop.wait(0.005)

    sampler = threading.Thread(target=sample)
    sampler.start()
    started = base.now_ns()
    try:
        result = action()
    finally:
        elapsed_ms = (base.now_ns() - started) / 1e6
        stop.set()
        sampler.join()
    return result, elapsed_ms, peak_kib / 1024


def measured_setup(workspace: Path, worker: int) -> tuple[Path, dict[str, Any]]:
    setup, completion_ms = base.setup_file(workspace, worker)
    return setup, {"completion_ms": completion_ms, "peak_rss_mib": 0.0}


def precondition() -> Path:
    workspace = base.make_workspaces()[0]
    base.setup_file(workspace, 1)
    return workspace


def expected_errors(round_index: int) -> int:
    return int(round_index == 1)


def lsp_diagnostics(client: base.LspClient, uri: str, version: int) -> int:
    client.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
    matching = [
        notification["params"].get("diagnostics", [])
        for notification in client.notifications
        if notification.get("method") == "textDocument/publishDiagnostics"
        and notification.get("params", {}).get("version") == version
    ]
    diagnostics = matching[-1] if matching else []
    return sum(diagnostic.get("severity") == 1 for diagnostic in diagnostics)


def run_lsp(strategy: str, repetition: int) -> list[dict[str, Any]]:
    workspace = precondition()
    client = base.LspClient(workspace)
    rows: list[dict[str, Any]] = []
    client.request("initialize", {
        "processId": os.getpid(),
        "rootUri": workspace.resolve().as_uri(),
        "capabilities": {"workspace": {}},
    })
    client.notify("initialized", {})
    versions = [0, 0, 0, 0]
    open_files: set[int] = set()
    try:
        for round_index in range(3):
            for worker in range(1, 5):
                valid, invalid = base.sources(worker)
                source = invalid if round_index == 1 else valid
                target = workspace / "MathmuxFixture" / f"Worker{worker}.lean"
                uri = target.resolve().as_uri()
                versions[worker - 1] += 1
                version = versions[worker - 1]
                client.notifications.clear()

                def check() -> int:
                    if worker in open_files:
                        client.notify("textDocument/didChange", {
                            "textDocument": {"uri": uri, "version": version},
                            "contentChanges": [{"text": source}],
                        })
                    else:
                        client.notify("textDocument/didOpen", {"textDocument": {
                            "uri": uri,
                            "languageId": "lean4",
                            "version": version,
                            "text": source,
                        }})
                        open_files.add(worker)
                    return lsp_diagnostics(client, uri, version)

                errors, elapsed_ms, peak_rss_mib = measure_call(check, client.process.pid)
                rows.append({
                    "strategy": strategy,
                    "repetition": repetition,
                    "visit": round_index * 4 + worker,
                    "round": round_index + 1,
                    "worker": worker,
                    "state": ["valid", "error", "repair"][round_index],
                    "cold_file": round_index == 0 or strategy == "lsp-close-on-switch",
                    "completion_ms": elapsed_ms,
                    "peak_rss_mib": peak_rss_mib,
                    "resident_rss_mib": base.process_tree_rss_kib(client.process.pid) / 1024,
                    "errors": errors,
                    "expected_errors": expected_errors(round_index),
                    "correct": (errors > 0) == bool(expected_errors(round_index)),
                })
                if strategy == "lsp-close-on-switch":
                    client.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
                    open_files.remove(worker)
    finally:
        client.close()
    return rows


def run_lean(strategy: str, repetition: int) -> list[dict[str, Any]]:
    workspace = precondition()
    setups: dict[int, Path] = {}
    rows: list[dict[str, Any]] = []
    for round_index in range(3):
        for worker in range(1, 5):
            valid, invalid = base.sources(worker)
            source = invalid if round_index == 1 else valid
            target = workspace / "MathmuxFixture" / f"Worker{worker}.lean"
            target.write_text(source)
            setup_ms = 0.0
            setup_peak = 0.0
            if strategy == "lean-setup-each" or worker not in setups:
                setup, measured_setup_result = measured_setup(workspace, worker)
                setups[worker] = setup
                setup_ms = measured_setup_result["completion_ms"]
                setup_peak = measured_setup_result["peak_rss_mib"]
            measured = base.run(
                [str(base.LEAN), str(target), "--json", f"--setup={setups[worker]}"],
                cwd=workspace,
            )
            errors = int(measured["exit_code"] != 0)
            rows.append({
                "strategy": strategy,
                "repetition": repetition,
                "visit": round_index * 4 + worker,
                "round": round_index + 1,
                "worker": worker,
                "state": ["valid", "error", "repair"][round_index],
                "cold_file": strategy == "lean-setup-each" or round_index == 0,
                "completion_ms": setup_ms + measured["completion_ms"],
                "peak_rss_mib": max(setup_peak, measured["peak_rss_mib"]),
                "resident_rss_mib": 0.0,
                "errors": errors,
                "expected_errors": expected_errors(round_index),
                "correct": errors == expected_errors(round_index),
            })
    return rows


def run_snapshots(repetition: int) -> list[dict[str, Any]]:
    workspace = precondition()
    snapshots: dict[int, Path] = {}
    rows: list[dict[str, Any]] = []
    for round_index in range(3):
        for worker in range(1, 5):
            valid, invalid = base.sources(worker)
            source = invalid if round_index == 1 else valid
            target = workspace / "MathmuxFixture" / f"Worker{worker}.lean"
            target.write_text(source)
            setup_ms = 0.0
            setup_peak = 0.0
            snapshot = workspace / ".work" / f"Worker{worker}.{round_index}.incr"
            if worker not in snapshots:
                setup, setup_result = measured_setup(workspace, worker)
                setup_ms = setup_result["completion_ms"]
                setup_peak = setup_result["peak_rss_mib"]
                command = [str(base.LEAN), str(target), "--json", f"--setup={setup}",
                           f"--incr-save={snapshot}"]
            else:
                command = [str(base.LEAN), str(target), "--json",
                           f"--incr-load={snapshots[worker]}", f"--incr-save={snapshot}"]
            measured = base.run(command, cwd=workspace)
            snapshots[worker] = snapshot
            errors = int(measured["exit_code"] != 0)
            rows.append({
                "strategy": "cli-snapshot",
                "repetition": repetition,
                "visit": round_index * 4 + worker,
                "round": round_index + 1,
                "worker": worker,
                "state": ["valid", "error", "repair"][round_index],
                "cold_file": round_index == 0,
                "completion_ms": setup_ms + measured["completion_ms"],
                "peak_rss_mib": max(setup_peak, measured["peak_rss_mib"]),
                "resident_rss_mib": 0.0,
                "errors": errors,
                "expected_errors": expected_errors(round_index),
                "correct": errors == expected_errors(round_index),
            })
    return rows


def run_lake(repetition: int) -> list[dict[str, Any]]:
    workspace = precondition()
    rows: list[dict[str, Any]] = []
    for round_index in range(3):
        for worker in range(1, 5):
            valid, invalid = base.sources(worker)
            target = workspace / "MathmuxFixture" / f"Worker{worker}.lean"
            target.write_text(invalid if round_index == 1 else valid)
            measured = base.run(
                [str(base.LAKE), "build", f"MathmuxFixture.Worker{worker}"],
                cwd=workspace,
            )
            errors = int(measured["exit_code"] != 0)
            rows.append({
                "strategy": "lake-build",
                "repetition": repetition,
                "visit": round_index * 4 + worker,
                "round": round_index + 1,
                "worker": worker,
                "state": ["valid", "error", "repair"][round_index],
                "cold_file": round_index == 0,
                "completion_ms": measured["completion_ms"],
                "peak_rss_mib": measured["peak_rss_mib"],
                "resident_rss_mib": 0.0,
                "errors": errors,
                "expected_errors": expected_errors(round_index),
                "correct": errors == expected_errors(round_index),
            })
    return rows


def summarize(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    summary = []
    for strategy in STRATEGIES:
        group = [row for row in rows if row["strategy"] == strategy]
        if not group:
            continue
        cold = [row["completion_ms"] for row in group if row["cold_file"]]
        revisit = [row["completion_ms"] for row in group if not row["cold_file"]]
        totals = [sum(row["completion_ms"] for row in group if row["repetition"] == repetition)
                  for repetition in sorted({row["repetition"] for row in group})]
        summary.append({
            "strategy": strategy,
            "n": len(group),
            "correct": all(row["correct"] for row in group),
            "median_visit_ms": round(statistics.median(row["completion_ms"] for row in group), 3),
            "median_cold_ms": round(statistics.median(cold), 3) if cold else None,
            "median_revisit_ms": round(statistics.median(revisit), 3) if revisit else None,
            "median_12_visit_total_ms": round(statistics.median(totals), 3),
            "peak_rss_mib": round(max(row["peak_rss_mib"] for row in group), 1),
            "max_observed_resident_rss_mib": round(
                max(row["resident_rss_mib"] for row in group), 1
            ),
        })
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20260824)
    parser.add_argument("--strategies", nargs="+", choices=STRATEGIES, default=STRATEGIES)
    args = parser.parse_args()
    random.seed(args.seed)
    base.RESULTS.mkdir(exist_ok=True)
    rows: list[dict[str, Any]] = []
    for repetition in range(args.repetitions):
        order = args.strategies.copy()
        random.shuffle(order)
        for strategy in order:
            print(f"repetition {repetition + 1}/{args.repetitions}: {strategy}", flush=True)
            if strategy.startswith("lsp-"):
                rows.extend(run_lsp(strategy, repetition))
            elif strategy.startswith("lean-"):
                rows.extend(run_lean(strategy, repetition))
            elif strategy == "cli-snapshot":
                rows.extend(run_snapshots(repetition))
            else:
                rows.extend(run_lake(repetition))
    raw_path = base.RESULTS / "switching_raw.jsonl"
    raw_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    with (base.RESULTS / "switching_raw.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = summarize(rows)
    (base.RESULTS / "switching_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (base.RESULTS / "switching_run.json").write_text(json.dumps({
        "machine": base.machine(),
        "seed": args.seed,
        "repetitions": args.repetitions,
        "files": 4,
        "rounds": ["valid", "error", "repair"],
        "cold_visit_share": 1 / 3,
        "strategies": args.strategies,
    }, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return int(not all(row["correct"] for row in rows))


if __name__ == "__main__":
    raise SystemExit(main())
