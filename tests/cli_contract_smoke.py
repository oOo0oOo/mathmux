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
    source = 'import Lean\nstructure Impossible where\n  witness : False\ntheorem a_admitted_empty : ¬ Nonempty Impossible := by sorry\ntheorem impossible_empty : ¬ Nonempty Impossible := by\n  intro h\n  cases h with | intro x => exact x.witness\ndef forgetInput (_n : Nat) : Nat := 0\ntheorem needsHypothesis (n : Nat) (h : n = 0) : n + 0 = 0 := by simpa using h\nexample (n : Nat) : n + 0 = 0 := by\n  sorry\n'
    (root / 'Fixture.lean').write_text(source)
    source_fixture = 'import Lean\nnamespace Demo\nvariable\n  {α : Type}\n    [Inhabited α]\nvariable (α) in\n/-- Own documentation. -/\ndef identityValue : α := default\n\n/-- Neighbor documentation. -/\n@[simp]\ntheorem longProof : True := by\n' + ('  -- ' + 'λ' * 250 + '\n') * 70 + '  exact True.intro\nend Demo\n'
    (root / 'SourceFixture.lean').write_text(source_fixture)
    contract_fixture = "import Lean\nstructure Parent where\n  datum : Nat\nstructure Child extends Parent where\n  good : datum = 0 := by trivial\nstructure InheritedOnly extends Parent\ndef manyInputs {A B C D E F G H I J K L M : Type} (n : Nat) : Nat := n\nexample : True := by trivial\n"
    (root / 'ContractFixture.lean').write_text(contract_fixture)
    (root / 'AttributeFixture.lean').write_text('import Lean\nnamespace AttributeFixture\n@[simp]\ntheorem simp (n : Nat) : n = n := rfl\nend AttributeFixture\n')

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
        for subject in ['Child', 'InheritedOnly']:
            fields = probe(subject + ' fields')
            assert 'inherited obligations are omitted' in fields and 'Extends: Parent' in fields, fields
        constructor = probe('ContractFixture.lean:8 #inspect Child.mk')
        assert 'data input toParent' in constructor and 'proof assumption good' in constructor, constructor
        many = probe('ContractFixture.lean:8 #inspect manyInputs')
        assert 'data input n' in many, many
        many_ref = next(line.removeprefix('ref: ') for line in many.splitlines() if line.startswith('ref: '))
        many_full = run([binary, 'show', many_ref, '--all'], ws).stdout
        assert 'data input M' in many_full and 'additional inputs omitted' not in many_full, many_full
        assert many_full.index('data input n') < many_full.index('data input A'), many_full
        attribute_signature = probe('AttributeFixture.simp signature')
        assert '(n : Nat) : n = n' in attribute_signature and '] theorem simp' not in attribute_signature, attribute_signature
        short = probe('Demo.identityValue source')
        assert '[Inhabited α]' in short and 'Own documentation.' in short, short
        assert 'Neighbor documentation.' not in short, short
        assert 'All source snapshot lines shown.' in short, short
        searched = run([binary, 'search', 'Demo.longProof source'], ws).stdout
        assert 'lines not shown' in searched and 'Continue:' in searched, searched
        searched_ref = next(line.removeprefix('ref: ') for line in searched.splitlines() if line.startswith('ref: '))
        assert 'exact True.intro' in run([binary, 'show', searched_ref, '--all'], ws).stdout
        detail = probe('Demo.longProof source')
        assert 'lines not shown' in detail and 'Continue:' in detail and '@[simp]' in detail, detail
        assert 'λ' * 250 in detail, detail
        source_ref = next(line.removeprefix('ref: ') for line in detail.splitlines() if line.startswith('ref: '))
        full = run([binary, 'show', source_ref, '--all'], ws).stdout
        assert 'exact True.intro' in full and 'λ' * 250 in full, full
        (ws / 'SourceFixture.lean').write_text(source_fixture.replace('exact True.intro', 'exact .intro'))
        fresh = probe(source_ref + ' source')
        fresh_ref = next(line.removeprefix('ref: ') for line in fresh.splitlines() if line.startswith('ref: '))
        assert fresh_ref != source_ref, fresh
        assert 'exact .intro' in run([binary, 'show', fresh_ref, '--all'], ws).stdout
        assert 'exact True.intro' in run([binary, 'show', source_ref, '--all'], ws).stdout
        (ws / 'SourceFixture.lean').write_text(source_fixture)
        for query in ['Demo.longProof find exact', source_ref + ' find exact']:
            found = probe(query)
            assert '   83    exact True.intro' in found, found
        found = probe('Demo.longProof find nonexistentNeedle')
        assert 'No literal matches' in found, found
        outline = probe('Demo.longProof outline')
        assert '   83    exact True.intro' in outline, outline
        assert 'premises retained' in probe('Impossible assumptions')
        assert 'obstruction candidate' in probe('Impossible evidence')
        detail = probe('Fixture.lean:11 #inspect forgetInput')
        assert 'absent from definition body' in detail, detail
        detail = probe('Fixture.lean:11 #apply needsHypothesis n')
        assert 'n = 0' in detail, detail
        failed = run([binary, 'probe', 'Fixture.lean:11 #apply True.intro'], ws, ok=False)
        failure = failed.stdout + failed.stderr
        assert failed.returncode != 0 and 'first type difference' in failure, failure
        assert 'Full diagnostic: mathmux show' in failure, failure
        failed_ref = next(line.removeprefix('ref: ') for line in failure.splitlines() if line.startswith('ref: '))
        full = run([binary, 'show', failed_ref, '--all'], ws).stdout
        assert 'Full Lean diagnostic:' in full and 'Tactic `apply` failed' in full, full
        detail = probe('Fixture.lean:11 Impossible evidence')
        assert 'Lean inspection succeeded' in detail, detail
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'matching project-source/configuration snapshot' in detail, detail
        (ws / '.mathmux-evidence.json').write_text(json.dumps({'version': 1, 'links': [{'subject': 'Impossible', 'replacement': 'Nat', 'examples': ['forgetInput'], 'explanation': 'Only an advisory example.'}]}))
        detail = probe('Impossible examples')
        assert 'forgetInput' in detail and 'advisory' in detail, detail
        examples_ref = next(line.removeprefix('ref: ') for line in detail.splitlines() if line.startswith('ref: '))
        selected = probe(examples_ref + '#1 assumptions')
        assert 'forgetInput' in selected and '_n' in selected, selected
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'project-authored route' in detail, detail
        (ws / 'Fixture.lean').write_text(source + '\n-- changed snapshot\n')
        detail = run([binary, 'search', 'Impossible'], ws).stdout
        assert 'matching project-source/configuration snapshot' not in detail, detail
        (ws / 'Fixture.lean').write_text(source)
        detail = probe('Fixture.lean:11 #inspect needsHypothesis')
        assert 'proof assumption h' in detail, detail
        (ws / 'Fixture').mkdir(exist_ok=True)
        (ws / 'Fixture/BadDependency.lean').write_text('def broken : Nat := "not a Nat"\n')
        (ws / 'Fixture/DependencyGuard.lean').write_text('import Fixture.BadDependency\ntheorem guard : True := by trivial\n')
        run(['git', 'add', 'Fixture/BadDependency.lean', 'Fixture/DependencyGuard.lean'], ws)
        run(['git', 'commit', '-m', 'isolated dependency error fixture'], ws)
        dependency_check = run([binary, 'check', 'Fixture/DependencyGuard.lean'], ws, ok=False)
        assert dependency_check.returncode != 0, dependency_check.stdout
        import re
        check_ref = re.search(r'\bc[0-9]+\b', dependency_check.stdout + dependency_check.stderr).group(0)
        dependency_detail = run([binary, 'show', check_ref], ws).stdout
        assert 'blocked target: Fixture/DependencyGuard.lean' in dependency_detail, dependency_detail
        assert 'Dependency Lean error' in dependency_detail and 'target not elaborated' in dependency_detail, dependency_detail
        assert 'Fixture/BadDependency.lean:' in dependency_detail, dependency_detail
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
        print('CLI smoke passed: inherited fields, default constructor inspection, complete stored input lists, dependency Lean error attribution, complete source snapshots/continuations/freshness, assumptions, source evidence, Lean evidence, inspection, application, cached evidence/invalidation, authored examples/routes, structured empty telemetry/provenance, unchanged source.')
    finally:
        try:
            daemon.wait(timeout=15)
        except subprocess.TimeoutExpired:
            daemon.terminate()
            daemon.wait(timeout=5)
        log.close()
        if sibling.exists():
            shutil.rmtree(sibling)
