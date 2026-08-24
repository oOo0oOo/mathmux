#!/usr/bin/env python3
"""Measure exploratory Lean LSP feedback before full-file completion."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import random
import statistics
import time
from typing import Any, Callable

import experiment as base


PROBES = ["partial-diagnostic", "plain-goal", "hover", "full-diagnostics"]


def source(revision: int, tail_size: int) -> str:
    lines = [
        "module",
        "",
        "import MathmuxFixture.Shared",
        "",
        "namespace MathmuxFixture.Worker1",
        "",
        "open MathmuxFixture",
        "",
        f"def probeRevision : Nat := {revision}",
        "",
        "example : (0 : Nat) = 1 := by",
        "  rfl",
        "",
        f"example (n : Nat) : n + {revision + 1} = {revision + 1} + n := by",
        "  omega",
        "",
        "#check rowland",
        "",
    ]
    for index in range(tail_size):
        lines.extend([
            f"example : probeRevision + {index} = {revision + index} := by",
            "  norm_num [probeRevision]",
            "",
        ])
    lines.extend(["end MathmuxFixture.Worker1", ""])
    return "\n".join(lines)


def position(text: str, needle: str) -> dict[str, int]:
    offset = text.index(needle)
    before = text[:offset]
    return {
        "line": before.count("\n"),
        "character": len(before.rsplit("\n", 1)[-1]),
    }


def next_notification(
    client: base.LspClient,
    predicate: Callable[[dict[str, Any]], bool],
    timeout: float = 180,
) -> dict[str, Any]:
    started = time.monotonic()
    while True:
        message = client.pop()
        if message is None:
            if time.monotonic() - started > timeout:
                raise TimeoutError("notification")
            if client.selector.select(0.02):
                chunk = os.read(client.stdout.fileno(), 65536)
                if not chunk:
                    raise RuntimeError("LSP exited while waiting for notification")
                client.buffer.extend(chunk)
            continue
        if "method" in message and "id" in message:
            client.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
        elif "method" in message:
            client.notifications.append(message)
            if predicate(message):
                return message


def diagnostics(client: base.LspClient, uri: str, version: int) -> list[dict[str, Any]]:
    current: list[dict[str, Any]] = []
    for notification in client.notifications:
        if notification.get("method") != "textDocument/publishDiagnostics":
            continue
        params = notification.get("params", {})
        if params.get("uri") != uri or params.get("version") != version:
            continue
        update = params.get("diagnostics", [])
        if params.get("isIncremental"):
            current.extend(update)
        else:
            current = update.copy()
    return current


def error_count(items: list[dict[str, Any]]) -> int:
    return sum(item.get("severity") == 1 for item in items)


def run_probe(
    client: base.LspClient,
    uri: str,
    probe: str,
    repetition: int,
    version: int,
    tail_size: int,
    report_delay_ms: int,
) -> dict[str, Any]:
    text = source(version, tail_size)
    client.notifications.clear()
    started = base.now_ns()
    client.notify("textDocument/didChange", {
        "textDocument": {"uri": uri, "version": version},
        "contentChanges": [{"text": text}],
    })
    result: Any = None
    if probe == "partial-diagnostic":
        result = next_notification(client, lambda message:
            message.get("method") == "textDocument/publishDiagnostics"
            and message.get("params", {}).get("version") == version
            and error_count(message.get("params", {}).get("diagnostics", [])) > 0)
    elif probe == "plain-goal":
        result = client.request("$/lean/plainGoal", {
            "textDocument": {"uri": uri},
            "position": position(text, "omega"),
        }).get("result")
    elif probe == "hover":
        result = client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": position(text, "rowland"),
        }).get("result")
    else:
        client.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
    response_ms = (base.now_ns() - started) / 1e6
    if probe != "full-diagnostics":
        client.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
    full_ms = (base.now_ns() - started) / 1e6
    final_errors = error_count(diagnostics(client, uri, version))
    if probe == "partial-diagnostic":
        response_ok = error_count(result.get("params", {}).get("diagnostics", [])) > 0
        response_detail = {
            "version": result.get("params", {}).get("version"),
            "incremental": result.get("params", {}).get("isIncremental"),
            "errors": error_count(result.get("params", {}).get("diagnostics", [])),
        }
    elif probe == "plain-goal":
        expected_goal = f"n + {version + 1} = {version + 1} + n"
        response_ok = bool(result and any(
            expected_goal in goal for goal in result.get("goals", [])
        ))
        response_detail = result
    elif probe == "hover":
        response_ok = result is not None
        response_detail = {"present": result is not None}
    else:
        response_ok = True
        response_detail = None
    return {
        "probe": probe,
        "repetition": repetition,
        "version": version,
        "report_delay_ms": report_delay_ms,
        "tail_declarations": tail_size,
        "response_ms": response_ms,
        "full_ms": full_ms,
        "lead_ms": full_ms - response_ms,
        "response_ok": response_ok,
        "response_detail": response_detail,
        "final_errors": final_errors,
        "correct": response_ok and final_errors == 1,
    }


def supersede_probe(
    client: base.LspClient,
    uri: str,
    version: int,
    tail_size: int,
    report_delay_ms: int,
) -> dict[str, Any]:
    old_version = version + 1
    new_version = version + 2
    old_text = source(old_version, tail_size)
    new_text = source(new_version, tail_size)
    client.notifications.clear()
    started = base.now_ns()
    for next_version, text in [(old_version, old_text), (new_version, new_text)]:
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": next_version},
            "contentChanges": [{"text": text}],
        })
    result = client.request("$/lean/plainGoal", {
        "textDocument": {"uri": uri},
        "position": position(new_text, "omega"),
    }).get("result")
    response_ms = (base.now_ns() - started) / 1e6
    client.request("textDocument/waitForDiagnostics", {"uri": uri, "version": new_version})
    full_ms = (base.now_ns() - started) / 1e6
    published_versions = [
        notification.get("params", {}).get("version")
        for notification in client.notifications
        if notification.get("method") == "textDocument/publishDiagnostics"
    ]
    expected_goal = f"n + {new_version + 1} = {new_version + 1} + n"
    current_goal = bool(result and any(
        expected_goal in goal for goal in result.get("goals", [])
    ))
    all_diagnostics_versioned = all(version is not None for version in published_versions)
    published_version_counts = {
        str(published_version): published_versions.count(published_version)
        for published_version in sorted(set(published_versions))
    }
    return {
        "report_delay_ms": report_delay_ms,
        "old_version": old_version,
        "new_version": new_version,
        "response_ms": response_ms,
        "full_ms": full_ms,
        "current_goal": current_goal,
        "published_version_counts": published_version_counts,
        "stale_diagnostics": old_version in published_versions,
        "all_diagnostics_versioned": all_diagnostics_versioned,
        "final_errors": error_count(diagnostics(client, uri, new_version)),
        "correct": current_goal and all_diagnostics_versioned
        and error_count(diagnostics(client, uri, new_version)) == 1,
    }


def summarize(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    summary = []
    for report_delay_ms in sorted({row["report_delay_ms"] for row in rows}):
        for probe in PROBES:
            group = [row for row in rows
                     if row["report_delay_ms"] == report_delay_ms and row["probe"] == probe]
            summary.append({
                "report_delay_ms": report_delay_ms,
                "probe": probe,
                "n": len(group),
                "correct": all(row["correct"] for row in group),
                "median_response_ms": round(
                    statistics.median(row["response_ms"] for row in group), 3
                ),
                "median_full_ms": round(statistics.median(row["full_ms"] for row in group), 3),
                "median_lead_ms": round(statistics.median(row["lead_ms"] for row in group), 3),
            })
    return summary


def run_delay(args: argparse.Namespace, report_delay_ms: int) -> tuple[
    list[dict[str, Any]], dict[str, Any]
]:
    workspace = base.make_workspaces()[0]
    base.setup_file(workspace, 1)
    client = base.LspClient(workspace, report_delay_ms)
    uri = (workspace / "MathmuxFixture" / "Worker1.lean").resolve().as_uri()
    rows: list[dict[str, Any]] = []
    try:
        client.request("initialize", {
            "processId": os.getpid(),
            "rootUri": workspace.resolve().as_uri(),
            "capabilities": {
                "workspace": {},
                "lean": {"incrementalDiagnosticSupport": True},
            },
        })
        client.notify("initialized", {})
        initial = source(0, args.tail_declarations)
        client.notify("textDocument/didOpen", {"textDocument": {
            "uri": uri,
            "languageId": "lean4",
            "version": 0,
            "text": initial,
        }})
        client.request("textDocument/waitForDiagnostics", {"uri": uri, "version": 0})
        version = 0
        for repetition in range(args.repetitions):
            probes = PROBES.copy()
            random.shuffle(probes)
            for probe in probes:
                version += 1
                print(
                    f"delay {report_delay_ms}ms, repetition "
                    f"{repetition + 1}/{args.repetitions}: {probe}",
                    flush=True,
                )
                rows.append(run_probe(
                    client, uri, probe, repetition, version, args.tail_declarations,
                    report_delay_ms,
                ))
        contract = supersede_probe(
            client, uri, version, args.tail_declarations, report_delay_ms
        )
    finally:
        client.close()
    return rows, contract


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--tail-declarations", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20260824)
    parser.add_argument("--report-delays", nargs="+", type=int, default=[0, 200])
    args = parser.parse_args()
    random.seed(args.seed)
    rows: list[dict[str, Any]] = []
    contracts = []
    for report_delay_ms in args.report_delays:
        delay_rows, contract = run_delay(args, report_delay_ms)
        rows.extend(delay_rows)
        contracts.append(contract)
    base.RESULTS.mkdir(exist_ok=True)
    (base.RESULTS / "exploratory_raw.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows)
    )
    summary = summarize(rows)
    (base.RESULTS / "exploratory_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (base.RESULTS / "exploratory_contract.json").write_text(
        json.dumps(contracts, indent=2) + "\n"
    )
    (base.RESULTS / "exploratory_run.json").write_text(json.dumps({
        "machine": base.machine(),
        "repetitions": args.repetitions,
        "tail_declarations": args.tail_declarations,
        "seed": args.seed,
        "server_report_delays_ms": args.report_delays,
        "incremental_diagnostic_support": True,
    }, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return int(not all(row["correct"] for row in rows)
               or not all(contract["correct"] for contract in contracts))


if __name__ == "__main__":
    raise SystemExit(main())
