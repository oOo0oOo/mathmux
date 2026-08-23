#!/usr/bin/env python3
"""Run the Mathmux dirty-file checker experiment. Standard library only."""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import json
import os
from pathlib import Path
import platform
import random
import selectors
import shutil
import signal
import statistics
import subprocess
import threading
import time
from typing import Any


ROOT = Path(__file__).resolve().parent
WORK = ROOT / ".work"
RESULTS = ROOT / "results"
LAKE = Path.home() / ".elan" / "bin" / "lake"
LEAN = Path.home() / ".elan" / "bin" / "lean"
BENCH = ROOT / ".lake" / "build" / "bin" / "mathmuxBench"
PLUGIN = ROOT / ".lake" / "build" / "lib" / "libmathmux_MathmuxBenchServer.so"
HEADER = {
    "imports": [{
        "module": "MathmuxFixture.Shared",
        "importAll": False,
        "isExported": True,
        "isMeta": False,
    }],
    "isModule": True,
}
BACKENDS = ["language-full", "language-commands", "io-incremental", "lsp-standard",
            "lsp-custom", "cli-snapshot", "compacted-region", "lake-build"]


def now_ns() -> int:
    return time.monotonic_ns()


def process_tree_rss_kib(root_pid: int) -> int:
    children: dict[int, list[int]] = {}
    rss: dict[int, int] = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text()
            fields = stat[stat.rfind(")") + 2:].split()
            pid, ppid = int(entry.name), int(fields[1])
            children.setdefault(ppid, []).append(pid)
            for line in (entry / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    rss[pid] = int(line.split()[1])
                    break
        except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError):
            pass
    total, pending, seen = 0, [root_pid], set()
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        total += rss.get(pid, 0)
        pending.extend(children.get(pid, []))
    return total


def run(command: list[str], *, cwd: Path, stdin: str | None = None,
        env: dict[str, str] | None = None,
        timeout: float = 180.0) -> dict[str, Any]:
    started = now_ns()
    process = subprocess.Popen(command, cwd=cwd, env=env,
                               stdin=subprocess.PIPE if stdin is not None else None,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True)
    peak = 0
    timed_out = False
    if stdin is not None:
        assert process.stdin
        process.stdin.write(stdin)
        process.stdin.close()
    while process.poll() is None:
        peak = max(peak, process_tree_rss_kib(process.pid))
        if (now_ns() - started) / 1e9 > timeout:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.005)
    stdout = process.stdout.read() if process.stdout else ""
    stderr = process.stderr.read() if process.stderr else ""
    code = process.wait()
    return {"completion_ms": (now_ns() - started) / 1e6, "peak_rss_mib": peak / 1024,
            "exit_code": code, "timed_out": timed_out, "stdout": stdout, "stderr": stderr}


def setup_file(workspace: Path, worker: int) -> tuple[Path, float]:
    target = workspace / "MathmuxFixture" / f"Worker{worker}.lean"
    setup = workspace / ".work" / f"Worker{worker}.setup.json"
    setup.parent.mkdir(exist_ok=True)
    started = now_ns()
    result = subprocess.run([LAKE, "setup-file", str(target), "-"], cwd=workspace,
                            input=json.dumps(HEADER), text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"setup-file failed in {workspace}: {result.stderr}")
    setup.write_text(result.stdout)
    return setup, (now_ns() - started) / 1e6


def sources(worker: int) -> tuple[str, str]:
    valid = (ROOT / "MathmuxFixture" / f"Worker{worker}.lean").read_text()
    marker = f"{worker * 11} + n"
    invalid = valid.replace(marker, f"{worker * 11 + 1} + n", 1)
    if valid == invalid:
        raise RuntimeError(f"could not make fixed error edit for Worker{worker}")
    return valid, invalid


def body(source: str) -> str:
    lines = source.splitlines(keepends=True)
    return "".join(lines[4:])


def make_workspaces() -> list[Path]:
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir()
    workspaces = []
    for worker in range(1, 5):
        ws = WORK / f"worker{worker}"
        ws.mkdir()
        for name in ["lean-toolchain", "lakefile.lean", "lake-manifest.json", "MathmuxFixture.lean"]:
            shutil.copy2(ROOT / name, ws / name)
        shutil.copytree(ROOT / "MathmuxFixture", ws / "MathmuxFixture")
        (ws / ".lake").mkdir()
        (ws / ".lake" / "packages").symlink_to(ROOT / ".lake" / "packages")
        workspaces.append(ws)
    return workspaces


def reset_workspaces(workspaces: list[Path]) -> None:
    for ws in workspaces:
        for worker in range(1, 5):
            shutil.copy2(ROOT / "MathmuxFixture" / f"Worker{worker}.lean",
                         ws / "MathmuxFixture" / f"Worker{worker}.lean")
        shutil.copy2(ROOT / "MathmuxFixture" / "Shared.lean",
                     ws / "MathmuxFixture" / "Shared.lean")
        scratch = ws / ".work"
        if scratch.exists():
            shutil.rmtree(scratch)


class Backend:
    def __init__(self, workspace: Path, worker: int):
        self.workspace, self.worker = workspace, worker
        self.setup: Path | None = None
        self.prepare_ms = 0.0
        self.pid: int | None = None

    def prepare(self) -> None:
        self.setup, self.prepare_ms = setup_file(self.workspace, self.worker)

    def check(self, source: str, version: int) -> dict[str, Any]:
        raise NotImplementedError

    def shutdown(self) -> None:
        pass


class JsonBackend(Backend):
    def __init__(self, workspace: Path, worker: int, mode: str):
        super().__init__(workspace, worker)
        self.mode = mode
        self.process: subprocess.Popen[str] | None = None

    def prepare(self) -> None:
        super().prepare()
        lean_path = subprocess.check_output([LAKE, "env", "printenv", "LEAN_PATH"],
                                            cwd=self.workspace, text=True).strip()
        env = {**os.environ, "LEAN_PATH": lean_path}
        self.process = subprocess.Popen([BENCH, "server", self.mode], cwd=self.workspace, env=env,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, text=True, start_new_session=True)
        self.pid = self.process.pid
        valid, _ = sources(self.worker)
        primed = self.check(valid, 0)
        self.prepare_ms += primed["completion_ms"]

    def check(self, source: str, version: int) -> dict[str, Any]:
        assert self.process and self.process.stdin and self.process.stdout
        request_source = source if self.mode == "full" else body(source)
        started = now_ns()
        self.process.stdin.write(json.dumps({"op": "check", "source": request_source,
            "staleSource": "", "reuse": True, "version": version}) + "\n")
        self.process.stdin.flush()
        response = json.loads(self.process.stdout.readline())
        return {"completion_ms": (now_ns() - started) / 1e6, "errors": response["errors"],
                "reported_version": response["version"], "reused": response["reused"],
                "ok": response["ok"] == (response["errors"] == 0)}

    def supersede(self, stale: str, current: str, version: int) -> bool:
        if self.mode != "full":
            return False
        assert self.process and self.process.stdin and self.process.stdout
        self.process.stdin.write(json.dumps({"op": "supersede", "staleSource": stale,
            "source": current, "reuse": True, "version": version}) + "\n")
        self.process.stdin.flush()
        return json.loads(self.process.stdout.readline())["version"] == version

    def shutdown(self) -> None:
        if self.process:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(self.process.pid, signal.SIGKILL)


class LspClient:
    def __init__(self, cwd: Path):
        self.process = subprocess.Popen([LAKE, "serve", "--", "-Dserver.reportDelayMs=0",
            f"--plugin={PLUGIN}=initialize_mathmux_MathmuxBench_ServerPlugin"], cwd=cwd,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            start_new_session=True)
        assert self.process.stdin and self.process.stdout
        self.stdin, self.stdout = self.process.stdin, self.process.stdout
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.stdout, selectors.EVENT_READ)
        self.buffer, self.next_id = bytearray(), 1
        self.notifications: list[dict[str, Any]] = []

    def send(self, message: dict[str, Any]) -> None:
        payload = json.dumps(message, separators=(",", ":")).encode()
        self.stdin.write(f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload)
        self.stdin.flush()

    def notify(self, method: str, params: dict[str, Any]) -> None:
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def pop(self) -> dict[str, Any] | None:
        end = self.buffer.find(b"\r\n\r\n")
        if end < 0:
            return None
        headers = self.buffer[:end].decode().split("\r\n")
        length = next(int(x.split(":", 1)[1]) for x in headers if x.lower().startswith("content-length"))
        start = end + 4
        if len(self.buffer) < start + length:
            return None
        result = json.loads(self.buffer[start:start + length])
        del self.buffer[:start + length]
        return result

    def request(self, method: str, params: dict[str, Any], timeout: float = 180) -> dict[str, Any]:
        ident, self.next_id = self.next_id, self.next_id + 1
        self.send({"jsonrpc": "2.0", "id": ident, "method": method, "params": params})
        started = time.monotonic()
        while True:
            message = self.pop()
            if message is None:
                if time.monotonic() - started > timeout:
                    raise TimeoutError(method)
                if self.selector.select(0.02):
                    chunk = os.read(self.stdout.fileno(), 65536)
                    if not chunk:
                        raise RuntimeError(f"LSP exited during {method}")
                    self.buffer.extend(chunk)
                continue
            if "method" in message and "id" in message:
                self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
            elif "method" in message:
                self.notifications.append(message)
            elif message.get("id") == ident:
                return message

    def close(self) -> None:
        try:
            self.request("shutdown", {}, 10)
            self.notify("exit", {})
            self.process.wait(timeout=10)
        except Exception:
            os.killpg(self.process.pid, signal.SIGKILL)


class LspBackend(Backend):
    def __init__(self, workspace: Path, worker: int, custom: bool):
        super().__init__(workspace, worker)
        self.custom = custom
        self.client: LspClient | None = None
        self.uri = (workspace / "MathmuxFixture" / f"Worker{worker}.lean").resolve().as_uri()

    def prepare(self) -> None:
        super().prepare()
        started = now_ns()
        self.client = LspClient(self.workspace)
        self.pid = self.client.process.pid
        self.client.request("initialize", {"processId": os.getpid(),
            "rootUri": self.workspace.resolve().as_uri(), "capabilities": {"workspace": {}}})
        self.client.notify("initialized", {})
        valid, _ = sources(self.worker)
        self.client.notify("textDocument/didOpen", {"textDocument": {"uri": self.uri,
            "languageId": "lean4", "version": 0, "text": valid}})
        self.client.request("textDocument/waitForDiagnostics", {"uri": self.uri, "version": 0})
        self.prepare_ms += (now_ns() - started) / 1e6

    def check(self, source: str, version: int) -> dict[str, Any]:
        assert self.client
        self.client.notifications.clear()
        self.client.notify("textDocument/didChange", {"textDocument": {"uri": self.uri,
            "version": version}, "contentChanges": [{"text": source}]})
        started = now_ns()
        if self.custom:
            response = self.client.request("$/mathmux/completeDiagnostics", {
                "textDocument": {"uri": self.uri}, "version": version})
            diagnostics = response.get("result", [])
        else:
            self.client.request("textDocument/waitForDiagnostics", {"uri": self.uri, "version": version})
            matching = [n["params"].get("diagnostics", []) for n in self.client.notifications
                if n.get("method") == "textDocument/publishDiagnostics"
                and n.get("params", {}).get("version") == version]
            diagnostics = matching[-1] if matching else []
        errors = sum(d.get("severity") == 1 for d in diagnostics)
        return {"completion_ms": (now_ns() - started) / 1e6, "errors": errors,
                "reported_version": version, "reused": True, "ok": "error" not in response if self.custom else True}

    def shutdown(self) -> None:
        if self.client:
            self.client.close()


class CliSnapshotBackend(Backend):
    def prepare(self) -> None:
        super().prepare()
        assert self.setup
        self.snapshot = self.workspace / ".work" / f"Worker{self.worker}.incr"
        target = self.workspace / "MathmuxFixture" / f"Worker{self.worker}.lean"
        measured = run([str(LEAN), str(target), "--json", f"--setup={self.setup}",
                        f"--incr-save={self.snapshot}"], cwd=self.workspace)
        self.prepare_ms += measured["completion_ms"]
        if measured["exit_code"]:
            raise RuntimeError(measured["stderr"])

    def check(self, source: str, version: int) -> dict[str, Any]:
        target = self.workspace / "MathmuxFixture" / f"Worker{self.worker}.lean"
        target.write_text(source)
        nxt = self.snapshot.with_name(f"{self.snapshot.name}.{version}")
        measured = run([str(LEAN), str(target), "--json", f"--incr-load={self.snapshot}",
                        f"--incr-save={nxt}"], cwd=self.workspace)
        self.snapshot = nxt
        return {**measured, "errors": int(measured["exit_code"] != 0),
                "reported_version": version, "reused": True, "ok": not measured["timed_out"] if "timed_out" in measured else True}


class RegionBackend(Backend):
    def prepare(self) -> None:
        super().prepare()
        self.region = self.workspace / ".work" / "prepared.region"
        lean_path = subprocess.check_output([LAKE, "env", "printenv", "LEAN_PATH"], cwd=self.workspace, text=True).strip()
        self.env = {**os.environ, "LEAN_PATH": lean_path}
        measured = run([str(BENCH), "region-save", str(self.region)], cwd=self.workspace,
                       env=self.env, timeout=30)
        self.prepare_ms += measured["completion_ms"]
        if measured["exit_code"]:
            reason = "timed out" if measured["timed_out"] else f"exit {measured['exit_code']}"
            raise RuntimeError(
                f"CompactedRegion environment save {reason}; peak RSS {measured['peak_rss_mib']:.1f} MiB")

    def check(self, source: str, version: int) -> dict[str, Any]:
        started = now_ns()
        process = subprocess.run([BENCH, "region-check", self.region], cwd=self.workspace,
            env=self.env, input=body(source), text=True, capture_output=True)
        response = json.loads(process.stdout.splitlines()[-1]) if process.stdout else {"errors": 1}
        return {"completion_ms": (now_ns() - started) / 1e6, "errors": response["errors"],
                "reported_version": version, "reused": True, "ok": process.returncode == 0}


class LakeBackend(Backend):
    def check(self, source: str, version: int) -> dict[str, Any]:
        target = self.workspace / "MathmuxFixture" / f"Worker{self.worker}.lean"
        target.write_text(source)
        measured = run([str(LAKE), "build", f"MathmuxFixture.Worker{self.worker}"], cwd=self.workspace)
        return {**measured, "errors": int(measured["exit_code"] != 0),
                "reported_version": version, "reused": True, "ok": True}


def backend(name: str, workspace: Path, worker: int) -> Backend:
    if name == "language-full": return JsonBackend(workspace, worker, "full")
    if name == "language-commands": return JsonBackend(workspace, worker, "commands")
    if name == "io-incremental": return JsonBackend(workspace, worker, "incremental")
    if name == "lsp-standard": return LspBackend(workspace, worker, False)
    if name == "lsp-custom": return LspBackend(workspace, worker, True)
    if name == "cli-snapshot": return CliSnapshotBackend(workspace, worker)
    if name == "compacted-region": return RegionBackend(workspace, worker)
    if name == "lake-build": return LakeBackend(workspace, worker)
    raise ValueError(name)


def run_parallel(backends: list[Backend], states: list[str], version: int) -> tuple[list[dict[str, Any]], float, float]:
    barrier = threading.Barrier(len(backends) + 1)
    def one(pair: tuple[Backend, str]) -> dict[str, Any]:
        barrier.wait()
        return pair[0].check(pair[1], version)
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(backends)) as pool:
        futures = [pool.submit(one, pair) for pair in zip(backends, states)]
        barrier.wait()
        started = now_ns()
        peak = 0
        while not all(f.done() for f in futures):
            peak = max(peak, process_tree_rss_kib(os.getpid()))
            time.sleep(0.005)
        results = [f.result() for f in futures]
    return results, (now_ns() - started) / 1e6, peak / 1024


def machine() -> dict[str, Any]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    return {"date": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "platform": platform.platform(),
            "logical_cores": os.cpu_count(), "ram_mib": round(os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") / 2**20),
            "lean": subprocess.check_output([LEAN, "--version"], text=True).strip(),
            "mathlib_revision": mathlib["rev"], "fixture_revision": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--seed", type=int, default=20260823)
    parser.add_argument("--backends", nargs="+", choices=BACKENDS, default=BACKENDS)
    parser.add_argument("--concurrency", nargs="+", type=int, choices=[1, 2, 4], default=[1, 2, 4])
    args = parser.parse_args()
    random.seed(args.seed)
    RESULTS.mkdir(exist_ok=True)
    subprocess.run([LAKE, "build", "mathmuxBench", "MathmuxBenchServer:shared"], cwd=ROOT, check=True)
    if not PLUGIN.exists():
        raise RuntimeError(f"plugin not found at {PLUGIN}")
    rows: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    disqualified: set[str] = set()
    for concurrency in args.concurrency:
        workspaces = make_workspaces()
        for worker in range(1, concurrency + 1):
            setup_file(workspaces[worker - 1], worker)
        order = args.backends.copy()
        random.shuffle(order)
        for name in order:
            if name in disqualified:
                continue
            reset_workspaces(workspaces)
            instances: list[Backend] = []
            try:
                for worker in range(1, concurrency + 1):
                    item = backend(name, workspaces[worker - 1], worker)
                    item.prepare()
                    instances.append(item)
                idle_rss = sum(process_tree_rss_kib(x.pid) for x in instances if x.pid) / 1024
                for repetition in range(args.repetitions):
                    for state_name, state_index in [("valid", 0), ("error", 1), ("repair", 0)]:
                        state_sources = [sources(i + 1)[state_index] for i in range(concurrency)]
                        version = repetition * 3 + {"valid": 1, "error": 2, "repair": 3}[state_name]
                        measured, wall_ms, peak = run_parallel(instances, state_sources, version)
                        for worker, result in enumerate(measured, 1):
                            expected_errors = int(state_name == "error")
                            rows.append({"backend": name, "concurrency": concurrency,
                                "repetition": repetition, "worker": worker, "state": state_name,
                                "completion_ms": result["completion_ms"], "wall_ms": wall_ms,
                                "throughput_per_s": concurrency * 1000 / wall_ms,
                                "peak_tree_rss_mib": peak, "idle_rss_mib": idle_rss,
                                "prepare_ms": instances[worker - 1].prepare_ms,
                                "errors": result["errors"], "expected_errors": expected_errors,
                                "correct": (result["errors"] > 0) == bool(expected_errors)
                                    and result["reported_version"] == version,
                                "reported_version": result["reported_version"]})
            except Exception as error:
                failures.append({"backend": name, "concurrency": str(concurrency), "error": repr(error)})
                disqualified.add(name)
            finally:
                for item in instances:
                    item.shutdown()
            if concurrency == 1:
                candidate_rows = [row for row in rows if row["backend"] == name]
                if candidate_rows and not all(row["correct"] for row in candidate_rows):
                    failures.append({"backend": name, "concurrency": "1",
                        "error": "disqualified by valid/error/repair correctness gate"})
                    disqualified.add(name)
                if name == "io-incremental" and name not in disqualified:
                    failures.append({"backend": name, "concurrency": "1",
                        "error": "disqualified: retained API has no in-flight cancel/supersede boundary"})
                    disqualified.add(name)
    raw = RESULTS / "raw.jsonl"
    raw.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    fields = list(rows[0]) if rows else []
    with (RESULTS / "raw.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fields)
        writer.writeheader(); writer.writerows(rows)
    summary = []
    for name in args.backends:
        for concurrency in args.concurrency:
            group = [r for r in rows if r["backend"] == name and r["concurrency"] == concurrency]
            if not group: continue
            summary.append({"backend": name, "concurrency": concurrency, "n": len(group),
                "correct": all(r["correct"] for r in group),
                "median_completion_ms": round(statistics.median(r["completion_ms"] for r in group), 3),
                "median_wall_ms": round(statistics.median(r["wall_ms"] for r in group), 3),
                "median_throughput_per_s": round(statistics.median(r["throughput_per_s"] for r in group), 3),
                "peak_tree_rss_mib": round(max(r["peak_tree_rss_mib"] for r in group), 1),
                "idle_rss_mib": round(max(r["idle_rss_mib"] for r in group), 1),
                "median_prepare_ms": round(statistics.median(r["prepare_ms"] for r in group), 3)})
    (RESULTS / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (RESULTS / "run.json").write_text(json.dumps({"machine": machine(), "seed": args.seed,
        "repetitions": args.repetitions, "failures": failures}, indent=2) + "\n")
    print(json.dumps({"rows": len(rows), "failures": failures, "summary": summary}, indent=2))
    return int(not rows)


if __name__ == "__main__":
    raise SystemExit(main())
