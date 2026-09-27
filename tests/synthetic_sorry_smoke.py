"""Real Lean/CLI rejection of suppressed section-binder errors, in a disposable repo.
Arguments: new mathmux binary, pinned Lean binary, optional pre-fix mathmux binary.
The optional binary seeds a real obsolete passing certificate before upgrade.
"""
import os, pathlib, re, shutil, signal, sqlite3, subprocess, sys, tempfile, time

binary = str(pathlib.Path(sys.argv[1]).resolve())
lean = pathlib.Path(sys.argv[2]).resolve()
old_binary = str(pathlib.Path(sys.argv[3]).resolve()) if len(sys.argv) > 3 else None
source = '''import Lean
class C (α : Type) where
  x : α
def T (α : Type) [C α] := α
instance instC : C Nat := ⟨0⟩
variable (n : T Nat)
attribute [-instance] instC
def foo := n
'''

with tempfile.TemporaryDirectory(prefix='mathmux-synthetic-sorry-') as tmp:
    root = pathlib.Path(tmp) / 'repo'
    root.mkdir()
    env = {**os.environ, 'PATH': str(lean.parent) + os.pathsep + os.environ['PATH'],
           'MATHMUX_ISSUE_DB': str(pathlib.Path(tmp) / 'telemetry.sqlite3'),
           'MATHMUX_IDLE_SECONDS': '300'}
    def run(*args, cwd=root, ok=True):
        result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=90)
        if ok:
            assert result.returncode == 0, (args, result.stdout, result.stderr)
        return result
    run('git', 'init', '-b', 'main')
    run('git', 'config', 'user.name', 'Test')
    run('git', 'config', 'user.email', 'test@example.invalid')
    version = run(str(lean), '--version').stdout.split('version ', 1)[1].split()[0].rstrip(',')
    (root / 'lean-toolchain').write_text('leanprover/lean4:v' + version + '\n')
    (root / 'lakefile.toml').write_text('name = "fixture"\n[[lean_lib]]\nname = "Fixture"\n')
    (root / 'Fixture.lean').write_text(source)
    run('git', 'add', '.')
    run('git', 'commit', '-m', 'fixture')
    # Establish that the missing failure is upstream, not a CLI rendering bug.
    native = run(str(lean), 'Fixture.lean')
    assert 'uses `sorry`' in native.stdout, native
    daemon = None
    ws = None
    def start(executable):
        process = subprocess.Popen([executable, '__daemon', '--repo', str(root)], env=env, start_new_session=True,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(100):
            if (root / '.git/mathmux/daemon.sock').exists():
                return process
            assert process.poll() is None, 'disposable daemon exited before startup'
            time.sleep(0.05)
        raise AssertionError('disposable daemon did not start')
    def stop(process):
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=10)
        # Only our idle disposable daemon; no live proof jobs exist here.
        (root / '.git/mathmux/daemon.sock').unlink(missing_ok=True)
    try:
        initial = old_binary or binary
        daemon = start(initial)
        run(initial, 'ws', 'create', 'test')
        with sqlite3.connect(root / '.git/mathmux/state.sqlite3') as state:
            ws = pathlib.Path(state.execute("SELECT path FROM workspaces WHERE name='test'").fetchone()[0])
        if old_binary:
            prior = run(old_binary, 'check', 'Fixture.lean', cwd=ws)
            assert prior.stdout.startswith('ok c'), prior
            stop(daemon)
            daemon = start(binary)
        rejected = run(binary, 'check', 'Fixture.lean', cwd=ws, ok=False)
        assert rejected.returncode != 0, rejected
        output = rejected.stdout + rejected.stderr
        assert 'synthetic sorry' in output and 'foo' in output and ':8:4:' in output, output
        ref = re.search(r'\bc\d+\b', output).group()
        saved = run(binary, 'show', ref, '--all', cwd=ws).stdout
        assert 'failed' in saved and 'synthetic sorry' in saved, saved
        # Repeating the request must retain the failed result, not the old pass.
        repeated = run(binary, 'check', 'Fixture.lean', cwd=ws, ok=False)
        assert repeated.returncode != 0 and 'synthetic sorry' in repeated.stdout + repeated.stderr, repeated
        (ws / 'Fixture.lean').write_text(source.replace('attribute [-instance] instC\n', ''))
        repaired = run(binary, 'check', 'Fixture.lean', cwd=ws)
        assert repaired.stdout.startswith('ok c') and 'synthetic sorry' not in repaired.stdout, repaired
        (ws / 'Fixture.lean').write_text('import Lean\nnoncomputable def draft : Nat := by sorry\n')
        draft = run(binary, 'check', 'Fixture.lean', cwd=ws)
        assert draft.stdout.startswith('ok c'), draft
        draft_ref = re.search(r'\bc\d+\b', draft.stdout).group()
        assert 'uses `sorry`' in run(binary, 'show', draft_ref, '--all', cwd=ws).stdout, draft
    finally:
        if daemon is not None and daemon.poll() is None:
            stop(daemon)
        if ws is not None:
            shutil.rmtree(ws.parent, ignore_errors=True)
print('Synthetic recovery rejected and retained; repaired source passes; explicit sorry remains a draft warning.'
      + (' Obsolete passing certificate rejected after upgrade.' if old_binary else ''))
