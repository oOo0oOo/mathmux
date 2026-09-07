"""Exercise the real Lean service, without a daemon or a formalization workspace.
Run with: python tests/lean_probe_smoke.py /path/to/pinned/lean
"""
import json
import os
import pathlib
import subprocess
import sys
import tempfile

service = pathlib.Path(__file__).resolve().parents[1] / 'src/MathmuxLeanService.lean'
source = '''import Lean
structure Impossible where
  witness : False
theorem impossible_empty : ¬ Nonempty Impossible := by
  intro h
  cases h with | intro x => exact x.witness
def forgetInput (_n : Nat) : Nat := 0
theorem admitted_empty : ¬ Nonempty Nat := by sorry
def implicitInput {α : Type} [Inhabited α] [Subsingleton α] : α := default
theorem needsHypothesis (n : Nat) (h : n = 0) : n + 0 = 0 := by simpa using h
example (n : Nat) : n + 0 = 0 := by
  sorry
'''
requests = []
def request(operation, term, line=12):
    requests.append(dict(operation=operation, source=source, file_name='ProbeFixture.lean',
                         version=len(requests)+1, line=line, column=0, input=term, names=[]))
request('inspect', 'impossible_empty')
request('inspect', 'Impossible')
request('inspect', 'forgetInput')
request('inspect', 'admitted_empty')
request('tactic', 'apply (needsHypothesis n)')
request('term', '(forgetInput 7 : Nat)')
request('reduce', 'forgetInput 7')
request('tactic', 'apply (True.intro)')
request('inspect', 'notADeclaration')
request('inspect', 'Impossible', line=99)
request('goal', '')
request('inspect', 'needsHypothesis')
request('inspect_evidence', 'impossible_empty')
request('inspect_evidence', 'admitted_empty')
request('inspect_evidence', 'needsHypothesis')
request('inspect', 'implicitInput')
with tempfile.TemporaryDirectory(prefix='mathmux-lean-probe-') as temp:
    setup = pathlib.Path(temp) / 'setup.json'
    setup.write_text(json.dumps(dict(name='ProbeFixture', package=None, isModule=False,
        imports=None, importArts={}, dynlibs=[], plugins=[], options={})))
    result = subprocess.run([sys.argv[1], '--run', str(service), 'file', str(setup)],
        input=''.join(json.dumps(r)+'\n' for r in requests), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90,
        env={**os.environ, "PATH": str(pathlib.Path(sys.argv[1]).resolve().parent) + os.pathsep + os.environ["PATH"]})
    assert result.returncode == 0, result.stderr + result.stdout
    responses = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
    assert len(responses) == len(requests), (result.stdout, result.stderr)
    for i in range(7):
        assert responses[i]['ok'], (i, responses[i])
    assert 'negative existence result' in responses[0]['detail'], responses[0]
    assert 'axioms:' in responses[0]['detail'], responses[0]
    assert 'constructor Impossible.mk' in responses[1]['detail'], responses[1]
    assert 'parameters absent from definition body' in responses[2]['detail'], responses[2]
    assert 'ADMITTED' in responses[3]['detail'], responses[3]
    assert 'n = 0' in responses[4]['detail'] and 'solved' not in responses[4]['detail'], responses[4]
    assert responses[6]['detail'].strip() == '0', responses[6]
    for i in range(7, 10):
        assert not responses[i]['ok'], (i, responses[i])
    assert 'n + 0 = 0' in responses[10]['detail'], responses[10]
    assert 'proof assumption h' in responses[11]['detail'], responses[11]
    assert 'data input n' in responses[11]['detail'], responses[11]
    evidence = json.loads(responses[12]['detail'])
    assert evidence['subject'] == 'Impossible' and evidence['conclusion'], evidence
    assert 'sorryAx' not in evidence['axioms'], evidence
    admitted = json.loads(responses[13]['detail'])
    assert 'sorryAx' in admitted['axioms'], admitted
    ordinary = json.loads(responses[14]['detail'])
    assert ordinary.get('subject') is None and len(ordinary['premises']) == 2, ordinary
    assert responses[15]['ok'], responses[15]
    assert 'instance input' in responses[15]['detail'], responses[15]
    assert 'instance assumption' in responses[15]['detail'], responses[15]
    assert '_hyg' not in responses[15]['detail'] and '._@.' not in responses[15]['detail'], responses[15]
    print('Lean probe smoke: 16 cases passed (obstruction, fields, unused input, axioms, application, small cases, failures, goal isolation, premise roles).')
