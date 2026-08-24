#!/usr/bin/env python3
"""Compare out-of-band Lean axiom and sorry audit mechanisms."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
from typing import Any

import experiment as base


MACRO_FIXTURE = """module

public import MathmuxFixture.Shared

public section

macro "hiddenHole" : term => `(by exact sorry)

end
"""

FIXTURE = """module

public import MathmuxFixture.Shared
public import MathmuxFixture.AxiomMacro

namespace MathmuxFixture.AxiomFixture

public section

axiom hiddenProof : True
axiom unusedAxiom : False

axiom A0 : Type
axiom A1 : Type
class C where
  a0 : A0
axiom A2 (_ : A1) : C

theorem clean : True := True.intro

noncomputable def usesChoice (h : Nonempty Nat) : Nat := Classical.choice h

theorem usesNativeDecide : 1 + 1 = 2 := by
  native_decide

theorem hiddenAxiomAlias : True := hiddenProof

noncomputable def typedAxiomUse (x : A1) : C := A2 x

theorem directSorry : True := by
  sorry

theorem admitted : True := by
  admit

theorem macroSorry : True := hiddenHole

set_option warn.sorry false in
theorem suppressedSorry : True := by
  sorry

private theorem privateSorry : True := by
  sorry

theorem indirectPrivateSorry : True := privateSorry

end

end MathmuxFixture.AxiomFixture
"""

ROOTS = [
    "clean",
    "usesChoice",
    "usesNativeDecide",
    "hiddenAxiomAlias",
    "typedAxiomUse",
    "directSorry",
    "admitted",
    "macroSorry",
    "suppressedSorry",
    "indirectPrivateSorry",
]


def report_source(command: str) -> str:
    commands = "\n".join(
        f"{command} MathmuxFixture.AxiomFixture.{root}" for root in ROOTS
    )
    return f"""module

import Mathlib.Util.PrintSorries
import Mathlib.Util.AssertNoSorry
import MathmuxFixture.AxiomFixture

{commands}
"""


def setup_file(workspace: Path, target: Path, imports: list[str]) -> tuple[Path, float]:
    header = {
        "imports": [{
            "module": module,
            "importAll": False,
            "isExported": False,
            "isMeta": False,
        } for module in imports],
        "isModule": True,
    }
    setup = workspace / ".work" / f"{target.stem}.setup.json"
    setup.parent.mkdir(exist_ok=True)
    started = base.now_ns()
    result = subprocess.run(
        [base.LAKE, "setup-file", str(target), "-"],
        cwd=workspace,
        input=json.dumps(header),
        text=True,
        capture_output=True,
    )
    if result.returncode:
        raise RuntimeError(result.stderr)
    setup.write_text(result.stdout)
    return setup, (base.now_ns() - started) / 1e6


def messages(result: dict[str, Any]) -> list[dict[str, Any]]:
    parsed = []
    for stream in [result["stdout"], result["stderr"]]:
        for line in stream.splitlines():
            try:
                parsed.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return parsed


def scan_source(source: str) -> list[dict[str, Any]]:
    hits = []
    for line_number, line in enumerate(source.splitlines(), 1):
        tokens = re.findall(r"\b(?:axiom|sorry|admit)\b", line)
        if tokens:
            hits.append({"line": line_number, "tokens": tokens, "text": line.strip()})
    return hits


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fresh-checker-timeout", type=float, default=30.0)
    args = parser.parse_args()
    workspace = base.make_workspaces()[0]
    macro_fixture = workspace / "MathmuxFixture" / "AxiomMacro.lean"
    macro_fixture.write_text(MACRO_FIXTURE)
    fixture = workspace / "MathmuxFixture" / "AxiomFixture.lean"
    fixture.write_text(FIXTURE)
    build = base.run(
        [str(base.LAKE), "build", "MathmuxFixture.AxiomFixture"],
        cwd=workspace,
    )
    build_output = build["stdout"] + build["stderr"]
    if build["exit_code"] != 0:
        raise RuntimeError(build_output)
    warning_lines = [
        line for line in build_output.splitlines()
        if "declaration uses" in line and "sorry" in line
    ]
    scan_hits = scan_source(FIXTURE)
    macro_scan_hits = scan_source(MACRO_FIXTURE)

    imports = [
        "Mathlib.Util.PrintSorries",
        "Mathlib.Util.AssertNoSorry",
        "MathmuxFixture.AxiomFixture",
    ]
    print_axioms_file = workspace / "MathmuxFixture" / "PrintAxioms.lean"
    print_axioms_file.write_text(report_source("#print axioms"))
    print_axioms_setup, print_axioms_setup_ms = setup_file(
        workspace, print_axioms_file, imports
    )
    print_sorries_file = workspace / "MathmuxFixture" / "PrintSorries.lean"
    print_sorries_file.write_text(report_source("#print sorries"))
    print_sorries_setup, print_sorries_setup_ms = setup_file(
        workspace, print_sorries_file, imports
    )
    assert_file = workspace / "MathmuxFixture" / "AssertNoSorry.lean"
    assert_file.write_text(report_source("assert_no_sorry"))
    assert_setup, assert_setup_ms = setup_file(workspace, assert_file, imports)

    hidden_source = fixture.with_suffix(".lean.hidden")
    fixture.rename(hidden_source)
    macro_fixture.rename(macro_fixture.with_suffix(".lean.hidden"))

    print_axioms = base.run(
        [str(base.LEAN), str(print_axioms_file), "--json", f"--setup={print_axioms_setup}"],
        cwd=workspace,
    )
    print_axioms["setup_ms"] = print_axioms_setup_ms
    print_axioms["total_ms"] = print_axioms_setup_ms + print_axioms["completion_ms"]
    print_sorries = base.run(
        [str(base.LEAN), str(print_sorries_file), "--json", f"--setup={print_sorries_setup}"],
        cwd=workspace,
    )
    print_sorries["setup_ms"] = print_sorries_setup_ms
    print_sorries["total_ms"] = print_sorries_setup_ms + print_sorries["completion_ms"]
    assert_no_sorry = base.run(
        [str(base.LEAN), str(assert_file), "--json", f"--setup={assert_setup}"],
        cwd=workspace,
    )
    assert_no_sorry["setup_ms"] = assert_setup_ms
    assert_no_sorry["total_ms"] = assert_setup_ms + assert_no_sorry["completion_ms"]
    module_checker = base.run(
        [str(base.LAKE), "env", "leanchecker", "-v", "MathmuxFixture.AxiomFixture"],
        cwd=workspace,
    )
    fresh_checker = base.run(
        [str(base.LAKE), "env", "leanchecker", "--fresh", "MathmuxFixture.AxiomFixture"],
        cwd=workspace,
        timeout=args.fresh_checker_timeout,
    )

    print_axioms_messages = messages(print_axioms)
    print_sorries_messages = messages(print_sorries)
    assert_messages = messages(assert_no_sorry)
    print_axioms_data = [message.get("data", "") for message in print_axioms_messages]
    print_sorries_data = [message.get("data", "") for message in print_sorries_messages]
    assert_data = [message.get("data", "") for message in assert_messages]
    axioms_text = "\n".join(print_axioms_data)
    expected_axiom_fragments = [
        "clean' does not depend on any axioms",
        "usesChoice' depends on axioms: [Classical.choice]",
        "usesNativeDecide' depends on axioms: [_private.",
        "native_decide.ax",
        "hiddenAxiomAlias' depends on axioms: [MathmuxFixture.AxiomFixture.hiddenProof]",
        "MathmuxFixture.AxiomFixture.A0",
        "MathmuxFixture.AxiomFixture.A1",
        "MathmuxFixture.AxiomFixture.A2",
        "directSorry' depends on axioms: [sorryAx]",
        "admitted' depends on axioms: [sorryAx]",
        "macroSorry' depends on axioms: [sorryAx]",
        "suppressedSorry' depends on axioms: [sorryAx]",
        "indirectPrivateSorry' depends on axioms: [sorryAx]",
    ]
    expected_sorry_failures = [
        "directSorry contains sorry",
        "admitted contains sorry",
        "macroSorry contains sorry",
        "suppressedSorry contains sorry",
        "indirectPrivateSorry contains sorry",
    ]
    validation = {
        "print_axioms_complete": all(
            fragment in axioms_text for fragment in expected_axiom_fragments
        ),
        "print_sorries_imported_false_negatives":
            print_sorries_data.count("Declarations are sorry-free!") == len(ROOTS),
        "assert_no_sorry_complete": all(
            any(fragment in message for message in assert_data)
            for fragment in expected_sorry_failures
        ),
        "suppressed_warning_absent": len(warning_lines) == 4,
        "target_scan_misses_macro_expansion": not any(
            "hiddenHole" in hit["text"] for hit in scan_hits
        ),
        "module_checker_accepts_axioms": module_checker["exit_code"] == 0,
        "fresh_checker_reaches_bound": fresh_checker["timed_out"],
    }
    results = {
        "machine": base.machine(),
        "fixture": {
            "roots": ROOTS,
            "source_hidden_before_audits": True,
            "source_scan_hits": scan_hits,
            "imported_macro_source_scan_hits": macro_scan_hits,
        },
        "build_warnings": {
            "exit_code": build["exit_code"],
            "completion_ms": build["completion_ms"],
            "warning_count": len(warning_lines),
            "warnings": warning_lines,
        },
        "print_axioms": {
            "exit_code": print_axioms["exit_code"],
            "setup_ms": print_axioms["setup_ms"],
            "completion_ms": print_axioms["completion_ms"],
            "total_ms": print_axioms["total_ms"],
            "messages": print_axioms_data,
        },
        "print_sorries": {
            "exit_code": print_sorries["exit_code"],
            "setup_ms": print_sorries["setup_ms"],
            "completion_ms": print_sorries["completion_ms"],
            "total_ms": print_sorries["total_ms"],
            "messages": print_sorries_data,
        },
        "assert_no_sorry": {
            "exit_code": assert_no_sorry["exit_code"],
            "setup_ms": assert_no_sorry["setup_ms"],
            "completion_ms": assert_no_sorry["completion_ms"],
            "total_ms": assert_no_sorry["total_ms"],
            "messages": assert_data,
        },
        "leanchecker": {
            "module_replay": {
                "exit_code": module_checker["exit_code"],
                "completion_ms": module_checker["completion_ms"],
                "peak_rss_mib": module_checker["peak_rss_mib"],
                "output": module_checker["stdout"] + module_checker["stderr"],
            },
            "fresh_replay": {
                "exit_code": fresh_checker["exit_code"],
                "completion_ms": fresh_checker["completion_ms"],
                "peak_rss_mib": fresh_checker["peak_rss_mib"],
                "timed_out": fresh_checker["timed_out"],
                "timeout_seconds": args.fresh_checker_timeout,
            },
        },
        "validation": validation,
    }
    base.RESULTS.mkdir(exist_ok=True)
    (base.RESULTS / "axiom_audit.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    return int(build["exit_code"] != 0 or print_axioms["exit_code"] != 0
               or not all(validation.values()))


if __name__ == "__main__":
    raise SystemExit(main())
