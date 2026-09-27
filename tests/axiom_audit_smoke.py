"""Audit real imported declarations. Run with the project-pinned Lean executable."""
import os, pathlib, subprocess, tempfile, sys
lean = pathlib.Path(sys.argv[1]).resolve()
rust = (pathlib.Path(__file__).resolve().parents[1] / 'src/validation.rs').read_text()
audit = rust.split('r#"import Lean\nimport Lean.Util.CollectAxioms',1)[1].split('"#',1)[0]
audit = 'import Lean\nimport Lean.Util.CollectAxioms' + audit
audit = audit.replace('{imports}', '{ module := `AuditFixture }').replace('{names}', '`AuditFixture').replace('{{','{').replace('}}','}')
with tempfile.TemporaryDirectory(prefix='mathmux-audit-repro-') as tmp:
 p = pathlib.Path(tmp)
 (p/'AuditFixture.lean').write_text('import Lean\naxiom forbidden : False\ntheorem inherited : False := forbidden\ntheorem admitted : False := by sorry\ntheorem inheritedSorry : False := admitted\n')
 env = {**os.environ, 'LEAN_PATH': tmp, 'PATH': str(lean.parent)+os.pathsep+os.environ['PATH']}
 c = subprocess.run([str(lean), '-o', 'AuditFixture.olean', 'AuditFixture.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert c.returncode == 0,c.stderr+c.stdout
 (p/'Audit.lean').write_text(audit)
 a = subprocess.run([str(lean), '--run', 'Audit.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert a.returncode == 1, a.stdout+a.stderr
 findings = {line for line in a.stdout.splitlines() if not line.startswith('MATHMUX_AUDIT_PROGRESS')}
 assert 'MATHMUX_AXIOM\tforbidden\tforbidden' in findings, a.stdout+a.stderr
 assert 'MATHMUX_AXIOM\tforbidden\tinherited' in findings, a.stdout+a.stderr
 assert 'MATHMUX_SORRY\tadmitted' in findings, a.stdout+a.stderr
 assert 'MATHMUX_SORRY\tinheritedSorry' in findings, a.stdout+a.stderr
 (p/'AuditFixture.lean').write_text('module\npublic import Lean\npublic axiom forbidden : False\npublic theorem inherited : False := forbidden\npublic theorem admitted : False := by sorry\npublic theorem inheritedSorry : False := admitted\n')
 c = subprocess.run([str(lean), '-o', 'AuditFixture.olean', 'AuditFixture.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert c.returncode == 0,c.stderr+c.stdout
 a = subprocess.run([str(lean), '--run', 'Audit.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert a.returncode == 1 and {line for line in a.stdout.splitlines() if not line.startswith('MATHMUX_AUDIT_PROGRESS')} == findings, a.stdout+a.stderr
 (p/'AuditFixture.lean').write_text('import Lean\ntheorem clean : True := True.intro\n')
 c = subprocess.run([str(lean), '-o', 'AuditFixture.olean', 'AuditFixture.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert c.returncode == 0,c.stderr+c.stdout
 a = subprocess.run([str(lean), '--run', 'Audit.lean'],cwd=p,env=env,text=True,capture_output=True)
 assert a.returncode == 0 and 'MATHMUX_AUDIT_PROGRESS' in a.stdout and 'MATHMUX_AXIOM' not in a.stdout and 'MATHMUX_SORRY' not in a.stdout, a.stdout+a.stderr
 print('Imported axiom audit smoke: forbidden axioms and transitive sorry detected; clean module passes.')
