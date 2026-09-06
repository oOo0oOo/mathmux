"""Isolated end-to-end CLI smoke. Arguments: mathmux binary, pinned lean binary."""
import json, os, pathlib, sqlite3, subprocess, tempfile, time, shutil, sys
binary = str(pathlib.Path(sys.argv[1]).resolve())
leanbin = str(pathlib.Path(sys.argv[2]).resolve().parent)
with tempfile.TemporaryDirectory(prefix='mmprobe-') as tmp:
    root = pathlib.Path(tmp) / 'repo'
    root.mkdir()
    env = {**os.environ, 'PATH': leanbin + os.pathsep + os.environ['PATH'], 'MATHMUX_ISSUE_DB': str(pathlib.Path(tmp) / 'telemetry.sqlite3'), 'MATHMUX_IDLE_SECONDS': '2', 'MATHMUX_ACTOR_ID': 'smoke-actor', 'MATHMUX_SESSION_ID': 'smoke-session'}

    def run(args, cwd=root, ok=True):
        p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=80)
        if ok and p.returncode:
            raise AssertionError((args, p.stdout, p.stderr))
        return p
    run(['git', 'init', '-b', 'main'])
    run(['git', 'config', 'user.name', 'Smoke'])
    run(['git', 'config', 'user.email', 'smoke@example.invalid'])
    version = run([str(pathlib.Path(leanbin) / 'lean'), '--version']).stdout.split('version ', 1)[1].split()[0].rstrip(',')
    (root / 'lean-toolchain').write_text('leanprover/lean4:v' + version + '\n')
    (root / 'lakefile.toml').write_text('name = "probe_fixture"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Fixture"\n')
    source = 'import Lean\nstructure Impossible where\n  witness : False\ntheorem impossible_empty : ¬ Nonempty Impossible := by\n  intro h\n  cases h with | intro x => exact x.witness\ndef forgetInput (_n : Nat) : Nat := 0\ntheorem needsHypothesis (n : Nat) (h : n = 0) : n + 0 = 0 := by simpa using h\nexample (n : Nat) : n + 0 = 0 := by\n  sorry\n'
    (root / 'Fixture.lean').write_text(source)
    run(['git', 'add', '.'])
    run(['git', 'commit', '-m', 'fixture'])
    log = open(pathlib.Path(tmp) / 'daemon.log', 'w+')
    daemon = subprocess.Popen([binary, '__daemon', '--repo', str(root)], env=env, stdout=log, stderr=log)
    sibling = root.parent / f'.mathmux-{root.name}'
    try:
        sock = root / '.git/mathmux/daemon.sock'
        for i in range(100):
            if sock.exists():
                break
            if daemon.poll() is not None:
                log.seek(0)
                raise AssertionError(log.read())
            time.sleep(0.05)
        run([binary, 'ws', 'create', 'smoke'])
        c = sqlite3.connect(root / '.git/mathmux/state.sqlite3')
        ws = pathlib.Path(c.execute("select path from workspaces where name='smoke'").fetchone()[0])
        c.close()

        def probe(q):
            return run([binary, 'probe', q], ws).stdout
        assert 'premises retained' in probe('Impossible assumptions')
        assert 'obstruction candidate' in probe('Impossible evidence')
        detail = probe('Fixture.lean:10 #inspect forgetInput')
        assert 'absent from definition body' in detail, detail
        detail = probe('Fixture.lean:10 #apply needsHypothesis n')
        assert 'n = 0' in detail, detail
        detail = probe('Fixture.lean:10 Impossible evidence')
        assert 'Lean inspection succeeded' in detail, detail
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'matching project-source/configuration snapshot' in detail, detail
        (ws / '.mathmux-evidence.json').write_text(json.dumps({'version': 1, 'links': [{'subject': 'Impossible', 'replacement': 'Nat', 'examples': ['forgetInput'], 'explanation': 'Only an advisory example.'}]}))
        detail = probe('Impossible examples')
        assert 'forgetInput' in detail and 'advisory' in detail, detail
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'project-authored route' in detail, detail
        (ws / 'Fixture.lean').write_text(source + '\n-- changed snapshot\n')
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'matching project-source/configuration snapshot' not in detail, detail
        (ws / 'Fixture.lean').write_text(source)
        detail = probe('Fixture.lean:10 #inspect needsHypothesis')
        assert 'proof assumption h' in detail, detail
        output = run([binary, 'search', 'DefinitelyAbsentName*'], ws).stdout
        reference = next(line.removeprefix('ref: ') for line in output.splitlines() if line.startswith('ref: '))
        db = sqlite3.connect(env['MATHMUX_ISSUE_DB'])
        # The daemon flushes the response before writing telemetry.
        row = None
        for _ in range(100):
            row = db.execute("select outcome_class,candidate_count,response_json from telemetry_events where verb='search' and reference=?", (reference,)).fetchone()
            if row is not None:
                break
            time.sleep(.05)
        assert row[0] == 'no_result' and row[1] == 0, row
        assert json.loads(row[2])['search_outcome']['result_count'] == 0, row
        event = json.loads(db.execute('select request_json from telemetry_events order by id desc limit 1').fetchone()[0])
        assert event['actor_id'] == 'smoke-actor' and event['session_id'] == 'smoke-session', event
        db.close()
        assert (ws / 'Fixture.lean').read_text() == source
        print('CLI smoke passed: assumptions, source evidence, Lean evidence, inspection, application, cached evidence/invalidation, authored examples/routes, structured empty telemetry/provenance, unchanged source.')
    finally:
        try:
            daemon.wait(timeout=15)
        except subprocess.TimeoutExpired:
            daemon.terminate()
            daemon.wait(timeout=5)
        log.close()
        if sibling.exists():
            shutil.rmtree(sibling)
