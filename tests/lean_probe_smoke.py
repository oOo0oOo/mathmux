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
def defaultProof (n : Nat) (h : n = 0 := by trivial) : Nat := n
def manyInputs {A B C D E F G H I J K L M : Type} (n : Nat) : Nat := n
example (n : Nat) : n + 0 = 0 := by
  sorry
'''
requests = []
def request(operation, term, line=14):
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
request('inspect', 'defaultProof')
request('inspect', 'manyInputs')
for _ in range(3):
    request('inspect', 'Nat.add', line=1)
request('inspect', 'manyInputs', line=1)
provenance_start = len(requests)
source = """import Lean
axiom unsafeResult : Nat → False
def wrapped (n : Nat) : False := unsafeResult n
theorem admittedTruth : True := by sorry
example (h : False) : True := by
  let hidden := unsafeResult 0
  have keep : False := hidden
  exact False.elim keep
example : True := by
  let hidden : True := by sorry
  have keep := hidden
  exact keep
"""
for term in ['(unsafeResult 0)', '(wrapped 0)', 'h', 'hidden', '(Nat.succ 0)', '(False.elim h : Nat)', '(id (by sorry : Nat))']:
    request('inspect', term, line=8)
local_definition_start = len(requests)
request('inspect', 'hidden', line=12)
request('tactic', 'exact hidden', line=12)
request('tactic', 'exact True.intro', line=12)
error_start = len(requests)
request('tactic', 'exact ?_', line=8)
request('tactic', 'exact (0 : Nat)', line=8)
request('tactic', 'run_tac Lean.Elab.Tactic.setGoals []', line=8)
request('tactic', 'sorry', line=8)
request('tactic', 'exact admittedTruth', line=8)
request('tactic', 'exact False.elim h', line=8)
request('tactic', 'exact True.intro', line=8)
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
    assert responses[3]['detail'].index('ADMITTED') < responses[3]['detail'].index('inputs (explicit first)'), responses[3]
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
    assert responses[16]['ok'] and 'proof assumption h' in responses[16]['detail'], responses[16]
    assert responses[17]['ok'], responses[17]
    assert responses[17]['detail'].find('data input n') < responses[17]['detail'].find('data input A'), responses[17]
    assert 'data input M' in responses[17]['detail'], responses[17]
    assert 'additional inputs omitted' not in responses[17]['detail'], responses[17]
    for response in responses[18:21]:
        assert response['ok'] and 'Nat → Nat → Nat' in response['detail'], response
    assert not responses[21]['ok'] and 'Unknown identifier' in str(responses[21]), responses[21]

    for offset in [0, 1, 3]:
        response = responses[provenance_start + offset]
        assert response['ok'] and 'axioms: unsafeResult' in response['detail'], response
    for offset in [2, 5]:
        response = responses[provenance_start + offset]
        assert response['ok'] and 'local assumption h: False' in response['detail'], response
    response = responses[provenance_start + 4]
    assert response['ok'] and 'axioms: none' in response['detail'], response
    assert 'local assumption' not in response['detail'], response
    response = responses[provenance_start + 6]
    assert response['ok'] and 'sorryAx' in response['detail'] and 'ADMITTED' in response['detail'], response
    assert response['detail'].index('ADMITTED') < response['detail'].index('inputs (explicit first)'), response
    for response in responses[local_definition_start:local_definition_start + 2]:
        assert response['ok'] and 'ADMITTED' in response['detail'], response
    response = responses[local_definition_start + 2]
    assert response['ok'] and response['detail'] == 'solved', response
    response = responses[error_start]
    assert not response['ok'] and 'synthesize placeholder' in response['detail'], response
    assert '⊢ True' in response['detail'] and 'abortTactic' not in response['detail'], response
    response = responses[error_start + 1]
    assert not response['ok'] and 'Type mismatch' in response['detail'], response
    assert responses[-5]['ok'] and 'INCOMPLETE' in responses[-5]['detail'], responses[-5]
    for response in responses[-4:-2]:
        assert response['ok'] and 'ADMITTED' in response['detail'], response
    assert responses[-2]['ok'] and responses[-2]['detail'] == 'solved', responses[-2]
    assert responses[-1]['ok'] and responses[-1]['detail'] == 'solved', responses[-1]
    print(f'Lean probe smoke: {len(responses)} cases passed, including expression provenance.')
