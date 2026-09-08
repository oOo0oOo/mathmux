"""Check real Lean profile coordinates. Usage: python tests/lean_profile_smoke.py LEAN"""
import json
import os
import pathlib
import subprocess
import sys
import tempfile

lean = pathlib.Path(sys.argv[1]).resolve()
service = pathlib.Path(__file__).resolve().parents[1] / 'src/MathmuxLeanService.lean'
sources = [
    'import Lean\ntheorem slow : True := by\n  run_tac do IO.sleep 120\n  trivial\ndef neighbor : Nat := 0\n',
    'import Lean\n-- Unicode comment: αβγ\nnamespace Demo\ntheorem slow : True := by\n  run_tac do IO.sleep 120\n  trivial\nend Demo\n',
]
with tempfile.TemporaryDirectory(prefix='mathmux-profile-smoke-') as temp:
    setup = pathlib.Path(temp) / 'setup.json'
    setup.write_text(json.dumps(dict(name='Fixture', package=None, isModule=False,
        imports=None, importArts={}, dynlibs=[], plugins=[], options={})))
    requests = [dict(operation='check', source=source, file_name='Fixture.lean',
        version=i + 1, line=1, column=0, input='', names=[])
        for i, source in enumerate(sources)]
    result = subprocess.run([str(lean), '--run', str(service), 'file', str(setup), '--profile'],
        input=''.join(json.dumps(r) + '\n' for r in requests), text=True,
        capture_output=True, timeout=90,
        env={**os.environ, 'PATH': str(lean.parent) + os.pathsep + os.environ['PATH']})
    assert result.returncode == 0, result.stdout + result.stderr
    responses = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
    assert len(responses) == len(sources), result.stdout
    for source, response in zip(sources, responses):
        assert response['ok'], response
        expected = next(i for i, line in enumerate(source.splitlines(), 1)
                        if line.startswith('theorem slow'))
        for kind in ['Elab.command', 'Elab.definition.value']:
            entries = [e for e in response['profile'] if e['kind'] == kind]
            assert entries, response
            assert any(e['line'] == expected and e['column'] == 1 for e in entries), entries
print('Lean profile smoke: 2 source-coordinate cases passed.')
