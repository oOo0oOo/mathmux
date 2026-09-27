"""Check disposable module setup metadata against the pinned Lake. Arg: Lean binary."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

lean_bin = Path(sys.argv[1]).resolve().parent
with tempfile.TemporaryDirectory(prefix="mathmux-metadata-") as tmp:
    root = Path(tmp)
    (root / "lakefile.toml").write_text('name = "metadata_test"\n[[lean_lib]]\nname = "Demo"\n')
    (root / "Demo.lean").write_text("def demo : Nat := 1\n")
    env = {**os.environ, "PATH": str(lean_bin) + os.pathsep + os.environ["PATH"]}

    def build():
        result = subprocess.run([str(lean_bin / "lake"), "build", "Demo"], cwd=root,
                                env=env, capture_output=True, text=True, timeout=60)
        assert result.returncode == 0, (result.stdout, result.stderr)

    build()
    trace = root / ".lake/build/lib/lean/Demo.trace"
    original = trace.read_bytes()
    setup = root / ".lake/build/ir/Demo.setup.json"
    setup.unlink()
    build()
    assert trace.read_bytes() == original, "removing scratch invalidated a cached module"
    assert not setup.exists(), "unchanged module unexpectedly compiled"
    (root / "Demo.lean").write_text("def demo : Nat := 2\n")
    build()
    assert setup.is_file(), "compilation did not recreate its setup scratch"
print("PASS: absent module setup scratch preserves reuse and is regenerated on compilation")
