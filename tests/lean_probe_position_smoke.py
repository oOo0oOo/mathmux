"""An exact local inspection must not wait for unrelated later elaboration.
Run with: python tests/lean_probe_position_smoke.py /path/to/pinned/lean
"""
import json
import os
import pathlib
import select
import subprocess
import sys
import tempfile
import time

lean = pathlib.Path(sys.argv[1]).resolve()
service = pathlib.Path(__file__).resolve().parents[1] / 'src/MathmuxLeanService.lean'
with tempfile.TemporaryDirectory(prefix='mathmux-probe-position-') as temp:
    setup = pathlib.Path(temp) / 'setup.json'
    setup.write_text(json.dumps(dict(name='ProbeFixture', package=None, isModule=False,
        imports=None, importArts={}, dynlibs=[], plugins=[], options={})))
    process = subprocess.Popen([str(lean), '--run', str(service), 'file', str(setup)],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env={**os.environ, 'PATH': str(lean.parent) + os.pathsep + os.environ['PATH']})

    def request(source, operation, term, line, column=0):
        process.stdin.write(json.dumps(dict(operation=operation, source=source,
            file_name='ProbeFixture.lean', version=line, line=line, column=column,
            input=term, names=[])) + '\n')
        process.stdin.flush()
        assert select.select([process.stdout], [], [], 45)[0], 'service response timed out'
        return json.loads(process.stdout.readline())

    try:
        warm = request('import Lean\n', 'term', 'Nat', 1)
        assert warm['ok'], warm
        source = 'import Lean\ndef early (n : Nat) : Nat := n\nrun_cmd do IO.sleep 6000\n'
        column = source.splitlines()[1].rindex('n') + 1
        start = time.monotonic()
        response = request(source, 'inspect', 'n', 2, column)
        elapsed = time.monotonic() - start
        assert response['ok'] and 'local input n: Nat' in response['detail'], response
        assert elapsed < 3, f'probe waited {elapsed:.2f}s for an unrelated six-second command'
        print(f'Positioned probe returned exact local context in {elapsed:.3f}s.')
    finally:
        process.terminate()
        process.wait(timeout=10)
