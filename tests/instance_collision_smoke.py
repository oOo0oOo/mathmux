"""Real Lean check warns about indexed cross-module generated instance names.
Arguments: development mathmux binary, pinned lean binary. Disposable repo only.
"""
import json, os, pathlib, shutil, sqlite3, subprocess, sys, tempfile, time
binary = str(pathlib.Path(sys.argv[1]).resolve())
lean = pathlib.Path(sys.argv[2]).resolve()
with tempfile.TemporaryDirectory(prefix='mathmux-collision-') as tmp:
    root = pathlib.Path(tmp) / 'repo'
    root.mkdir()
    env = {**os.environ, 'PATH': str(lean.parent) + os.pathsep + os.environ['PATH'],
           'MATHMUX_ISSUE_DB': str(pathlib.Path(tmp) / 'telemetry.sqlite3'), 'MATHMUX_IDLE_SECONDS': '2'}
    def run(*args, cwd=root, ok=True):
        result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=60)
        if ok: assert result.returncode == 0, (args, result.stdout, result.stderr)
        return result
    run('git', 'init', '-b', 'main')
    run('git', 'config', 'user.name', 'Test')
    run('git', 'config', 'user.email', 'test@example.invalid')
    version = run(str(lean), '--version').stdout.split('version ', 1)[1].split()[0].rstrip(',')
    (root / 'lean-toolchain').write_text('leanprover/lean4:v' + version + '\n')
    (root / 'lakefile.toml').write_text('name = "fixture"\n[[lean_lib]]\nname = "Fixture"\n')
    source = 'namespace CollisionFixture\nlocal instance : Inhabited Bool := ⟨true⟩\nend CollisionFixture\n'
    (root / 'Fixture').mkdir()
    (root / 'Fixture/Base.lean').write_text(source)
    (root / 'Fixture/Target.lean').write_text(source.replace('true', 'false'))
    (root / 'Fixture.lean').write_text('')
    run('git', 'add', '.')
    run('git', 'commit', '-m', 'fixture')
    daemon = subprocess.Popen([binary, '__daemon', '--repo', str(root)], env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(100):
        if (root / '.git/mathmux/daemon.sock').exists(): break
        assert daemon.poll() is None, 'disposable daemon exited before startup'
        time.sleep(0.05)
    run(binary, 'ws', 'create', 'test')
    state = sqlite3.connect(root / '.git/mathmux/state.sqlite3')
    wsref, workspace = state.execute("SELECT ref,path FROM workspaces WHERE name='test'").fetchone()
    state.close()
    ws = pathlib.Path(workspace)
    try:
        artifact = ws / '.lake/build/lib/lean/Fixture/Base.ilean'
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run('lake', 'env', 'lean', '-i', str(artifact), 'Fixture/Base.lean', cwd=ws)
        declaration = next(name for name in json.loads(artifact.read_text())['decls'] if '.inst' in name)
        # Initialize search, then seed the real artifact's declaration to isolate
        # check-time collision reporting from asynchronous index refresh timing.
        run(binary, 'search', 'Fixture/Base.lean:1-3', cwd=ws)
        index = sqlite3.connect(root / '.git/mathmux/search.sqlite3')
        index.execute("INSERT INTO search_fts(owner,origin,file,module,line,name,kind,signature,docs,body) VALUES(?,?,?,?,?,?,?,?,?,?)",
                      (f'artifacts:{wsref}', str(artifact), 'Fixture/Base.lean', 'Fixture.Base', 2, declaration, 'declaration', '', '', ''))
        index.commit()
        index.close()
        checked = run(binary, 'check', 'Fixture/Target.lean', cwd=ws)
        assert 'possible cross-module instance collision' in checked.stdout, (checked.stdout, declaration)
        assert declaration in checked.stdout and 'Fixture/Base.lean:2' in checked.stdout, checked.stdout
        ref = next(word for word in checked.stdout.split() if word.startswith('c') and word[1:].isdigit())
        assert 'possible cross-module instance collision' in run(binary, 'show', ref, '--wait', '--all', cwd=ws).stdout
        (ws / 'Fixture/Target.lean').write_text(source.replace('instance :', 'instance uniqueTarget :'))
        repaired = run(binary, 'check', 'Fixture/Target.lean', cwd=ws)
        assert 'collision' not in repaired.stdout, repaired.stdout
        # A passing focused check can depend on an unsubmitted source. The CLI
        # must reject a selective packet before any integration or index change.
        (ws / 'Fixture').mkdir(exist_ok=True)
        (ws / 'Fixture/Needed.lean').write_text('def needed : Nat := 7\n')
        (ws / 'Consumer.lean').write_text('import Fixture.Needed\ndef consumer : Nat := needed\n')
        run(binary, 'check', 'Consumer.lean', cwd=ws)
        before = run('git', 'rev-parse', 'HEAD').stdout
        rejected = run(binary, 'submit', 'Consumer.lean', cwd=ws, ok=False)
        assert rejected.returncode != 0 and 'Fixture/Needed.lean' in rejected.stderr, rejected
        assert 'nothing was staged or integrated' in rejected.stderr, rejected.stderr
        assert run('git', 'rev-parse', 'HEAD').stdout == before
        assert not (root / 'Consumer.lean').exists()
        run('git', 'diff', '--cached', '--quiet', cwd=ws)
    finally:
        # Wait for the disposable daemon before removing its writable metadata.
        try:
            daemon.wait(timeout=15)
        except subprocess.TimeoutExpired:
            daemon.terminate()
            daemon.wait(timeout=5)
        shutil.rmtree(ws.parent, ignore_errors=True)
print('Generated-instance collision warning and repair pass; wait/all combines; incomplete selective submission rejected without mutation')
