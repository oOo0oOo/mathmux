"""Isolated end-to-end CLI smoke. Arguments: mathmux binary, pinned lean binary."""
import json, os, pathlib, sqlite3, subprocess, tempfile, time, shutil, sys, shlex
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
    contract_fixture = "import Lean\nstructure Parent where\n  datum : Nat\nstructure Child extends Parent where\n  good : datum = 0 := by trivial\nstructure InheritedOnly\n  extends Parent\ndef manyInputs {A B C D E F G H I J K L M : Type} (n : Nat) : Nat := n\nexample : True := by trivial\n"
    (root / 'ContractFixture.lean').write_text(contract_fixture)
    (root / 'AttributeFixture.lean').write_text('import Lean\nnamespace AttributeFixture\n@[simp]\ntheorem simp (n : Nat) : n = n := rfl\nend AttributeFixture\n')

    (root / 'HomFixture.lean').write_text('namespace HomFixture\ndef Data := Nat\nabbrev Hom (A B : Type) := A → B\ninfixr:10 " ⟶ " => Hom\ntheorem hom_unique : Subsingleton (Data ⟶ Unit) := inferInstance\nend HomFixture\n')

    (root / 'LocalFixture.lean').write_text('namespace LocalFixture\nlocal instance defaultSeven : Inhabited Nat := ⟨7⟩\ndef chosen : Nat := default\nend LocalFixture\ndef outside : Nat := default\nexample : True := by trivial\n')

    (root / 'RootFixture.lean').write_text('namespace Outer\ntheorem _root_.Canonical.target : True := by trivial\nend Outer\n')

    (root / 'Options.lean').write_text('namespace Demo\nset_option autoImplicit false\nset_option pp.universes true in\nvariable (n : Nat) in\ndef target : Nat := n\ndef later : Nat := 2\ntheorem proofOption : True := by\n  set_option pp.all true in\n    exact True.intro\nend Demo\ndef outside : Nat := 3\n')

    (root / 'NotationFixture.lean').write_text('namespace NotationFixture\ndef positiveValue (x : {n : Nat // n > 0}) : Nat := x.val\nend NotationFixture\n')

    (root / 'FindFixture.lean').write_text('-- find a neighborhood\ndef target : Nat := 1\n')

    (root / 'GroupedFixture.lean').write_text('structure GroupedFixture where\n  (inner outer : Nat)\n  ordered : inner < outer\n')
    (root / 'SubscriptFixture.lean').write_text('theorem SubscriptFixture.inv_le_inv₀ (n : Nat) : n = n := rfl\n')
    signature_inputs = ' '.join(f'InputType{i}' for i in range(30))
    (root / 'SignatureFixture.lean').write_text('def SignatureFixture.longInputs {' + signature_inputs + ' : Type} (n : Nat) : Nat := n\n')
    (root / 'AliasFixture.lean').write_text('namespace AliasFixture\ntheorem current : True := True.intro\n@[deprecated (since := "2026-03-05")] alias old :=\n  current\nend AliasFixture\n')
    (root / 'FileHitFixture.lean').write_text('-- unique file sentinel phrase\nnamespace FileHitFixture\ndef first : Nat := 1\nend FileHitFixture\n')
    (root / 'ModuleFixture').mkdir()
    (root / 'ModuleFixture/Facts.lean').write_text('namespace ModuleFixture\ndef first : Nat := 1\nend ModuleFixture\n')

    (root / 'GroupFixture.lean').write_text('namespace GroupFixture\ntheorem target : True := by\n  have useful : True := True.intro\n  exact useful\nend GroupFixture\n')

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

        for literal in ['"error:"', '"unknown identifier"', '"ordinary"']:
            reduced = probe('Fixture.lean:11 #reduce ' + literal)
            assert literal in reduced, reduced

        regex_miss = run([binary, 'search', '/^zzScopeSentinelAbsent$/'], ws).stdout
        assert 'dependencies require an explicit scope' in regex_miss, regex_miss
        assert 'indexed alternatives (not regex matches)' in regex_miss, regex_miss

        wrong_path = run([binary, 'search', 'Missing/Elsewhere/SourceFixture.lean:1-4'], ws, ok=False)
        assert wrong_path.returncode and 'source file not found or ambiguous' in wrong_path.stderr, wrong_path
        assert 'source result' not in wrong_path.stdout, wrong_path.stdout

        escaped_name = run([binary, 'probe', r'Demo.identityValue\u0027 source'], ws, ok=False)
        assert escaped_name.returncode and 'literal characters' in escaped_name.stderr, escaped_name
        assert 'source snapshot' not in escaped_name.stdout, escaped_name.stdout

        subscript = run([binary, 'search', 'SubscriptFixture.inv_le_inv₀*'], ws).stdout
        assert 'SubscriptFixture.inv_le_inv₀' in subscript and 'weak coverage' not in subscript, subscript

        grouped_fields = probe('GroupedFixture fields')
        assert 'inner : Nat' in grouped_fields and 'outer : Nat' in grouped_fields, grouped_fields
        assert 'ordered : inner < outer' in grouped_fields, grouped_fields

        generated_seed = run([binary, 'search', 'Parent'], ws).stdout
        generated_ref = next(line.removeprefix('ref: ') for line in generated_seed.splitlines() if line.startswith('ref: '))
        with sqlite3.connect(root / '.git/mathmux/state.sqlite3') as generated_db:
            generated_hits = json.loads(generated_db.execute('select hits_json from searches where ref=?', (generated_ref,)).fetchone()[0])
            generated_hits[0].update(name='Parent.mk', kind='generated', signature=None, source=None)
            generated_db.execute('update searches set hits_json=? where ref=?', (json.dumps(generated_hits), generated_ref))
        unavailable = probe(generated_ref + '#1 source')
        assert 'Source unavailable' in unavailable and '#inspect Parent.mk' in unavailable, unavailable
        assert 'importing project file' in unavailable, unavailable
        inspected_generated = probe('ContractFixture.lean:9 #inspect Parent.mk')
        assert 'datum' in inspected_generated, inspected_generated

        alias_seed = run([binary, 'search', 'AliasFixture.current'], ws).stdout
        alias_ref = next(line.removeprefix('ref: ') for line in alias_seed.splitlines() if line.startswith('ref: '))
        # Model a compiled alias hit; source-only indexes do not generate aliases.
        with sqlite3.connect(root / '.git/mathmux/state.sqlite3') as alias_db:
            alias_hits = json.loads(alias_db.execute('select hits_json from searches where ref=?', (alias_ref,)).fetchone()[0])
            alias_hits[0].update(name='AliasFixture.old', kind='generated', signature=None, source=None, line=3)
            alias_db.execute('update searches set hits_json=? where ref=?', (json.dumps(alias_hits), alias_ref))
        alias_source = probe(alias_ref + '#1 source')
        assert '@[deprecated (since := "2026-03-05")] alias old :=' in alias_source, alias_source
        assert 'mathmux probe current source' in alias_source, alias_source
        assert 'AliasFixture.lean:3' in alias_source, alias_source
        assert 'theorem current : True' in probe('AliasFixture.current source')

        signature_preview = probe('manyInputs signature')
        assert '(n : Nat) : Nat' in signature_preview, signature_preview
        assert '{A B C D E F G H I J K L M : Type}' in signature_preview, signature_preview
        assert 'Full signature/context:' not in signature_preview, signature_preview
        signature_ref = next(line.removeprefix('ref: ') for line in signature_preview.splitlines() if line.startswith('ref: '))
        signature_full = run([binary, 'show', signature_ref, '--all'], ws).stdout
        assert '{A B C D E F G H I J K L M : Type}' in signature_full, signature_full

        long_signature = probe('SignatureFixture.longInputs signature')
        assert '(n : Nat) : Nat [context: 1 implicit/typeclass]' in long_signature, long_signature
        long_ref = next(line.removeprefix('ref: ') for line in long_signature.splitlines() if line.startswith('ref: '))
        assert f'Full signature/context: mathmux show {long_ref} --all' in long_signature, long_signature
        assert signature_inputs in run([binary, 'show', long_ref, '--all'], ws).stdout

        notation = run([binary, 'search', 'NotationFixture.positiveValue'], ws).stdout
        assert '(x : {n : Nat // n > 0}) : Nat' in notation, notation

        doc_range = run([binary, 'search', 'SourceFixture.lean:10-12'], ws).stdout
        assert 'Neighbor documentation' in doc_range and 'theorem longProof' in doc_range, doc_range
        assert 'identityValue' not in doc_range, doc_range

        usage_search = run([binary, 'search', 'Demo.identityValue usages'], ws).stdout
        assert 'Demo.identityValue' in usage_search, usage_search
        assert 'weak coverage' not in usage_search, usage_search
        assert 'indexed usages' in usage_search or 'used in' in usage_search, usage_search

        find_result = run([binary, 'search', 'FindFixture.lean find missing_token_xyz'], ws).stdout
        assert 'no results' in find_result, find_result

        module_outline = run([binary, 'search', 'ModuleFixture.Facts outline'], ws).stdout
        assert '1 declarations across' in module_outline and 'ModuleFixture.first' in module_outline, module_outline

        file_hit = run([binary, 'search', 'unique file sentinel phrase'], ws).stdout
        file_ref = next(line.removeprefix('ref: ') for line in file_hit.splitlines() if line.startswith('ref: '))
        file_signature = probe(file_ref + '#1 signature')
        assert 'File result has no declaration signature' in file_signature, file_signature
        assert 'mathmux search FileHitFixture.lean outline' in file_signature, file_signature
        file_outline = run([binary, 'search', 'FileHitFixture.lean outline'], ws).stdout
        assert 'FileHitFixture.first' in file_outline, file_outline

        grouped = run([binary, 'search', 'GroupFixture.lean /target/'], ws).stdout
        grouped_ref = next(line.removeprefix('ref: ') for line in grouped.splitlines() if line.startswith('ref: '))
        full_group = probe(grouped_ref + '#1 source')
        assert 'source snapshot (textual context; not elaborated)' in full_group, full_group
        assert 'have useful : True' in full_group and 'exact useful' in full_group, full_group

        case_recovery = run([binary, 'search', 'FindFixture.lean /[Cc]ompact|[Rr]ellich/'], ws).stdout
        assert 'indexed alternatives (not regex matches) for: compact rellich' in case_recovery, case_recovery

        past_end = run([binary, 'search', 'FindFixture.lean:140-187'], ws).stdout
        assert 'file has 2 lines' in past_end, past_end
        assert 'mathmux search FindFixture.lean:tail' in past_end, past_end
        recovered_tail = run([binary, 'search', 'FindFixture.lean:tail'], ws).stdout
        assert 'def target : Nat := 1' in recovered_tail, recovered_tail

        options = probe('Demo.target source')
        assert 'set_option autoImplicit false' in options, options
        assert 'set_option pp.universes true in' in options, options
        assert 'variable (n : Nat) in' in options, options
        later_options = probe('Demo.later source')
        assert 'set_option autoImplicit false' in later_options, later_options
        assert 'pp.universes' not in later_options, later_options
        navigation = run([binary, 'search', '/Own documentation/'], ws).stdout
        for _ in range(2):
            next_command = next(line.removeprefix('next: ') for line in navigation.splitlines() if line.startswith('next: '))
            args = shlex.split(next_command)
            assert args[:2] == ['mathmux', 'search'], next_command
            navigation = run([binary, *args[1:]], ws).stdout
        assert 'Demo.identityValue' in navigation, navigation

        local_source = probe('LocalFixture.chosen source')
        assert 'local instance declared at source line 2' in local_source, local_source
        assert 'Inhabited Nat := ⟨7⟩' in local_source, local_source
        assert 'defaultSeven' not in probe('outside source')
        reduced = probe('LocalFixture.lean:6 #reduce LocalFixture.chosen')
        assert '\n7\n' in reduced, reduced

        for subject in ['Child', 'InheritedOnly']:
            fields = probe(subject + ' fields')
            assert 'inherited obligations are omitted' in fields and 'Extends: Parent' in fields, fields
        inherited_signature = probe('InheritedOnly signature')
        assert 'extends Parent' in inherited_signature and 'generated parent projection' not in inherited_signature.lower(), inherited_signature

        for malformed in ['#inspect Nat.add #inspect Nat.zero', '#check (']:
            failed = run([binary, 'probe', 'ContractFixture.lean:1 ' + malformed], ws, ok=False)
            assert failed.returncode != 0, failed
            assert 'error probe result' in failed.stderr and 'expected' in failed.stderr, failed

        for _ in range(3):
            imported = probe('ContractFixture.lean:1 #inspect Nat.add')
            assert 'Nat → Nat → Nat' in imported, imported

        constructor = probe('ContractFixture.lean:9 #inspect Child.mk')
        assert 'data input toParent' in constructor and 'proof assumption good' in constructor, constructor
        many = probe('ContractFixture.lean:9 #inspect manyInputs')
        assert 'data input n' in many, many
        many_ref = next(line.removeprefix('ref: ') for line in many.splitlines() if line.startswith('ref: '))
        many_full = run([binary, 'show', many_ref, '--all'], ws).stdout
        assert 'data input M' in many_full and 'additional inputs omitted' not in many_full, many_full
        assert many_full.index('data input n') < many_full.index('data input A'), many_full
        rooted = probe('Canonical.target source')
        assert 'theorem _root_.Canonical.target' in rooted, rooted
        ordinary = probe('_root_.AttributeFixture.simp source')
        assert 'theorem simp (n : Nat)' in ordinary, ordinary

        searched_signature = run([binary, 'search', 'AttributeFixture.simp signature'], ws).stdout
        assert searched_signature.startswith('exact declaration\n'), searched_signature
        assert 'AttributeFixture.simp : (n : Nat) : n = n' in searched_signature, searched_signature

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
        detail = probe('HomFixture.Data evidence')
        assert 'subsingleton candidate' not in detail, detail
        detail = probe('HomFixture.hom_unique source')
        assert 'Subsingleton (Data ⟶ Unit)' in detail, detail
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
        # Repeated failures should expose existing recovery evidence, not only a link.
        recovery = ws / 'RepeatConversion.lean'
        recovery.write_text(
            'structure RecoveryBox where\n  run : Nat → Nat\n'
            'instance : CoeFun RecoveryBox (fun _ => Nat → Nat) := ⟨RecoveryBox.run⟩\n'
            'def recoverBox (b : RecoveryBox) : RecoveryBox := b\n'
            'def recoverFn (f : Nat → Nat) : Nat → Nat := f\n'
            'theorem recover_coe (b : RecoveryBox) : (recoverBox b : Nat → Nat) = recoverFn b := rfl\n'
            'example (b : RecoveryBox) (h : recoverBox b = b) : True := by\n'
            '  have hx : recoverFn b = (b : Nat → Nat) := by\n    rw [h]\n  trivial\n'
        )
        for attempt in range(3):
            if attempt:
                recovery.write_text(recovery.read_text() + f'\n-- attempt {attempt}\n')
            checked = run([binary, 'check', 'RepeatConversion.lean'], ws, ok=False)
            evidence = checked.stdout + checked.stderr
            assert checked.returncode != 0, evidence
            if attempt == 0:
                assert 'Possible conversion' not in evidence, evidence
        assert 'repeated blocker:' in evidence, evidence
        assert 'recover_coe :' in evidence and 'applicability unverified' in evidence, evidence
        recovery.write_text(recovery.read_text().replace('rw [h]', 'rw [← recover_coe b, h]'))
        run([binary, 'check', 'RepeatConversion.lean'], ws)

        # A late proof premise must survive a long inspection preview.
        types = ' '.join(f'AmbientType{i}' for i in range(35))
        inputs = ' '.join(f'parameter{i}' for i in range(12))
        (ws / 'PremisePriority.lean').write_text(
            'theorem conditional {' + types + ' : Type} (' + inputs + ' : Nat) '
            '(required : False) : False := required\nexample : True := by\n  trivial\n')
        run([binary, 'check', 'PremisePriority.lean'], ws)
        inspected = run([binary, 'probe', 'PremisePriority.lean:3 "#inspect conditional"'], ws).stdout
        assert 'proof assumption required: False' in inspected and 'result: False' in inspected, inspected
        assert '1 assumption fields, 0 not shown' in inspected, inspected
        inspect_ref = next(line.removeprefix('ref: ') for line in inspected.splitlines() if line.startswith('ref: '))
        full_inspection = run([binary, 'show', inspect_ref, '--all'], ws).stdout
        assert 'data input parameter11: Nat' in full_inspection, full_inspection
        assert 'data input AmbientType34: Type' in full_inspection, full_inspection
        assert 'proof assumption required: False' in full_inspection, full_inspection

        # Stored contracts must retain requirements beyond the compact preview budget.
        long_target = ' ∧ '.join(['True'] * 60 + ['TerminalRequirement'])
        (ws / 'LongEvidence.lean').write_text(
            'def TerminalRequirement : Prop := False\n'
            'theorem conditional (required : ' + long_target + ') : ' + long_target + ' := required\n'
            'example : True := by\n  trivial\n')
        run([binary, 'check', 'LongEvidence.lean'], ws)
        inspected = run([binary, 'probe', 'LongEvidence.lean:4 "#inspect conditional"'], ws).stdout
        inspect_ref = next(line.removeprefix('ref: ') for line in inspected.splitlines() if line.startswith('ref: '))
        full_inspection = run([binary, 'show', inspect_ref, '--all'], ws).stdout
        assert full_inspection.count('TerminalRequirement') >= 3, full_inspection
        assert '[truncated; inspect selected declaration source]' not in full_inspection, full_inspection
        assert len(inspected) < 2000 and 'show ' + inspect_ref + ' --all' in inspected, inspected

        # Structural similarity is not verified type applicability.
        (ws / 'TypeRelated.lean').write_text(
            'class RelatedLift (α β : Type) where\n  lift : α → β\n'
            'instance : RelatedLift Nat Bool := ⟨fun _ => true⟩\n'
            'example : True := by\n  trivial\n')
        run([binary, 'check', 'TypeRelated.lean'], ws)
        related = run([binary, 'search', 'type:RelatedLift Nat Nat'], ws).stdout
        assert 'RelatedLift Nat Bool' in related, related
        assert 'related (applicability unverified)' in related, related
        unavailable = run([binary, 'probe', 'TypeRelated.lean:5 "#synth RelatedLift Nat Nat"'], ws, ok=False)
        assert unavailable.returncode != 0, unavailable.stdout

        # Line-only term probes must use the requested proof's local scope.
        (ws / 'LocalScope.lean').write_text(
            'example (n : Nat) : n = n := by\n  rfl\n'
            'example (m : Bool) : True := by\n  trivial\n')
        run([binary, 'check', 'LocalScope.lean'], ws)
        for line, name, typename in [(2, 'n', 'Nat'), (4, 'm', 'Bool')]:
            for directive in ['#check', '#inspect']:
                local = run([binary, 'probe', f'LocalScope.lean:{line} "{directive} {name}"'], ws).stdout
                assert typename in local, local
        for line, name in [(2, 'm'), (4, 'n')]:
            unavailable = run([binary, 'probe', f'LocalScope.lean:{line} "#check {name}"'], ws, ok=False)
            assert unavailable.returncode != 0 and 'Unknown identifier' in unavailable.stderr + unavailable.stdout

        (ws / 'Suggestion.lean').write_text('import Lean\nexample : True ∧ True := by\n  sorry\n')
        suggested = probe('Suggestion.lean:3 "by simp?"')
        assert 'solved' in suggested and 'Try this:' in suggested and 'simp only' in suggested, suggested
        ordinary = probe('Suggestion.lean:3 "by exact ⟨True.intro, True.intro⟩"')
        assert 'solved' in ordinary and 'Try this:' not in ordinary, ordinary

        phase_header = 'import Lean\nclass Ready (α : Type) : Prop where\n  witness : True\ndef Requires (α : Type) [Ready α] : Prop := True\n'
        for body, hinted in [
            ('example : Requires Nat := by\n  letI : Ready Nat := ⟨True.intro⟩\n  trivial\n', True),
            ('example : True := by\n  have : Requires Nat := by sorry\n  trivial\n', False),
        ]:
            (ws / 'StatementScope.lean').write_text(phase_header + body)
            phase = run([binary, 'check', 'StatementScope.lean'], ws, ok=False)
            assert phase.returncode != 0, phase
            assert ('required in the declaration signature' in phase.stdout + phase.stderr) == hinted, phase

        # A missing imported file on committed main has an actionable recovery.
        (root / 'Fixture').mkdir(exist_ok=True)
        (root / 'Fixture/FreshDependency.lean').write_text('theorem freshFact : True := True.intro\n')
        (ws / 'FreshConsumer.lean').write_text('import Fixture.FreshDependency\nexample : True := freshFact\n')
        missing = run([binary, 'check', 'FreshConsumer.lean'], ws, ok=False)
        assert missing.returncode != 0, missing.stdout
        assert 'run mathmux sync' not in missing.stdout + missing.stderr  # uncommitted main
        run(['git', 'add', 'Fixture/FreshDependency.lean'])
        run(['git', 'commit', '-m', 'new shared dependency'])
        missing = run([binary, 'check', 'FreshConsumer.lean'], ws, ok=False)
        evidence = missing.stdout + missing.stderr
        assert missing.returncode != 0 and 'no such file or directory' in evidence, evidence
        assert 'Fixture/FreshDependency.lean is committed on managed main but missing here' in evidence, evidence
        assert 'run mathmux sync' in evidence, evidence
        run([binary, 'sync'], ws)
        restored = run([binary, 'check', 'FreshConsumer.lean'], ws)
        assert 'run mathmux sync' not in restored.stdout, restored.stdout

        # Synthetic stored profile isolates rendering from timing variability.
        db = sqlite3.connect(root / '.git/mathmux/state.sqlite3')
        ref = db.execute('select ref from check_runs order by created_at desc limit 1').fetchone()[0]
        entries = [{'line': 7, 'column': 1, 'kind': 'theorem', 'detail': 'costlyHotspot', 'durationMs': 13000.0}]
        entries += [{'line': 0, 'column': 0, 'kind': 'component' + str(i), 'detail': '', 'durationMs': float(100-i)} for i in range(20)]
        profile = {'planning_ms': 0, 'files': [{'target': 'FreshConsumer.lean', 'mode': 'profile', 'dependencies_ms': 1, 'cache_ms': 1, 'setup_ms': 1, 'elaborate_ms': 14000, 'total_ms': 14003, 'entries': entries}]}
        warnings = [{'kind': 'linter', 'text': 'irrelevant linter ' + str(i), 'context': None} for i in range(20)]
        db.execute('update check_runs set profile_json=?, linters_json=? where ref=?', (json.dumps(profile), json.dumps(warnings), ref))
        db.commit()
        db.close()
        result = run([binary, 'probe', ref + ' profile'], ws)
        assert 'costlyHotspot' in result.stdout and 'irrelevant linter' not in result.stdout
        qref = next(line[5:] for line in result.stdout.splitlines() if line.startswith('ref: '))
        full = run([binary, 'show', qref, '--all'], ws).stdout
        assert 'component19' in full and 'costlyHotspot' in full

    finally:
        try:
            daemon.wait(timeout=15)
        except subprocess.TimeoutExpired:
            daemon.terminate()
            daemon.wait(timeout=5)
        log.close()
        if sibling.exists():
            shutil.rmtree(sibling)
