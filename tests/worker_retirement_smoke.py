"""Isolated daemon retirement with a long waiter. Args: mathmux binary, pinned Lean."""
import json
import os
from pathlib import Path
import select
import signal
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())
lean_bin = Path(sys.argv[2]).resolve().parent
with tempfile.TemporaryDirectory(prefix="mathmux-retirement-") as tmp:
    root = Path(tmp) / "repo"
    root.mkdir()
    env = {**os.environ, "PATH": str(lean_bin) + os.pathsep + os.environ["PATH"],
           "MATHMUX_ISSUE_DB": str(Path(tmp) / "telemetry.db")}

    def run(args, cwd=root):
        result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, timeout=80)
        assert result.returncode == 0, (args, result.stdout, result.stderr)
        return result.stdout

    run(["git", "init", "-b", "main"])
    run(["git", "config", "user.name", "Smoke"])
    run(["git", "config", "user.email", "smoke@example.invalid"])
    version = run([str(lean_bin / "lean"), "--version"]).split("version ")[1].split()[0].rstrip(",")
    (root / "lean-toolchain").write_text("leanprover/lean4:v" + version + "\n")
    (root / "lakefile.toml").write_text('name = "retirement"\n[[lean_lib]]\nname = "Fixture"\n')
    (root / "Fixture.lean").write_text("theorem fixture : True := True.intro\n")
    run(["git", "add", "."])
    run(["git", "commit", "-m", "fixture"])
    log = open(Path(tmp) / "daemon.log", "w+")
    daemon = subprocess.Popen([binary, "__daemon", "--repo", str(root)], env=env, stdout=log, stderr=log)
    worker_pid = None
    waiter = None
    try:
        sock = root / ".git/mathmux/daemon.sock"
        deadline = time.monotonic() + 15
        while not sock.exists() and time.monotonic() < deadline:
            assert daemon.poll() is None
            time.sleep(0.05)
        assert sock.exists()
        run([binary, "ws", "create", "smoke"])
        db = sqlite3.connect(root / ".git/mathmux/state.sqlite3")
        workspace = db.execute("SELECT path FROM workspaces WHERE name='smoke'").fetchone()[0]
        run([binary, "check", "Fixture.lean"], workspace)
        processes = run(["ps", "-eo", "pid,ppid,args"])
        workers = [int(parts[0]) for line in processes.splitlines()
                   if len(parts := line.strip().split(None, 2)) == 3
                   and parts[1] == str(daemon.pid) and "lake env lean" in parts[2]]
        assert len(workers) == 1, workers
        worker_pid = workers[0]
        # Only this disposable fixture's database is changed. Hold a real show
        # stream open while the daemon retires, without running another proof.
        reference = db.execute("SELECT ref FROM check_runs LIMIT 1").fetchone()[0]
        db.execute("UPDATE check_runs SET status='running' WHERE ref=?", (reference,))
        db.commit()
        request = {"cwd": workspace, "command": {"verb": "show", "reference": reference,
                   "all": False, "wait": True, "wait_timeout": 60}}
        waiter = socket.socket(socket.AF_UNIX)
        waiter.settimeout(5)
        waiter.connect(str(sock))
        waiter.sendall(json.dumps(request).encode() + b"\n")
        stream = waiter.makefile("rb")
        assert "progress" in json.loads(stream.readline())
        with socket.socket(socket.AF_UNIX) as retire:
            retire.settimeout(5)
            retire.connect(str(sock))
            retire.sendall(json.dumps({"cwd": workspace, "build": "newer-test-build",
                "generation": 2**63 - 1, "command": {"verb": "status"}}).encode() + b"\n")
            assert json.loads(retire.makefile("rb").readline())["retry"]
        pidfd = os.pidfd_open(worker_pid)
        try:
            assert select.select([pidfd], [], [], 5)[0], "long waiter pinned an idle worker after retirement"
        finally:
            os.close(pidfd)
        assert daemon.poll() is None, "retirement interrupted the active waiter"
        db.execute("UPDATE check_runs SET status='passed' WHERE ref=?", (reference,))
        db.commit()
        while "progress" in (response := json.loads(stream.readline())):
            pass
        assert response["ok"], response
        stream.close()
        db.close()
        print("PASS: retirement releases idle Lean worker while preserving the active show waiter")
    finally:
        if waiter is not None:
            waiter.close()
        if daemon.poll() is None:
            daemon.terminate()
            daemon.wait(timeout=5)
        if worker_pid is not None:
            try:
                os.killpg(worker_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        log.close()
