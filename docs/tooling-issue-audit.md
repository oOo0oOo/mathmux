# MathMux issue audit, 2026-09-07

The operator requested resolution of all MathMux reports and investigation through
actual tool use. Four discovered project tracker databases were inspected: MathMux,
Atiyah–Singer, DeepDive, and oli-setup. Only Atiyah–Singer had open reports (i86–i93).
These are MathMux tracker identities, not Oli issue identities.

## Actual usage

The clean, dedicated audit workspace w67 was synchronized through `mathmux sync`
(u5717). No mathematical edits were authored and no active formalization workspace
or process was changed. Checks ran sequentially through MathMux:

| Reports | Current replay | Setup | Target Lean | Result |
|---|---|---:|---:|---|
| i86–i89 | c54025, original projected commutator target | 4,931 ms | 23,101 ms | passed |
| i90 | c54027, original projected commutator guard | 4,729 ms | 7,806 ms | passed |
| i91 | c54026, actual cotangent principal-symbol guard | 5,836 ms | 7,776 ms | passed |
| i92 | c54028, index-one operator principal-symbol target | 5,538 ms | 8,409 ms | passed |

The first four reports predate the warm dependency restoration change 06c0f94;
current replay verifies that their reported timeout no longer occurs. The later
three reports concern historical cold/dirty dependency preparation. They no longer
reproduce on current accepted sources and artifacts, but these replays do not
reconstruct the original artifact state or prove a general latency bound. Close
those three as historical, currently non-actionable reports, not as a newly fixed
performance regression. MathMux check certificates and Lake's compiled dependency
artifacts are distinct; a successful source check alone does not guarantee warm
Lake import preparation.

## Reproduced defects and changes

`mathmux show c53821` reproduced i93: an actual dependency syntax error was shown
under a failed guard and `Lean 0ms`, obscuring that the target never elaborated.
`mathmux probe 'c53821 goal'` correctly selected the dependency diagnostic. Show now
labels the requested file as a **blocked target**, identifies a dependency Lean
error during import preparation, and says to fix the reported dependency error
before retrying. Historical stored records benefit without rewriting them.

The timeout path also discarded the subprocess's output and suggested installing
a toolchain regardless of the cause. It now preserves the last eight nonempty
stderr lines (240 characters each), retains the typed timeout and process-group
cleanup, and reports incomplete preparation without inventing a missing-toolchain
diagnosis. This is additional diagnostic context, not a promise to eliminate cold
build costs or live progress streaming.

Validation includes a real timed child process with stderr output and cleanup;
a historical dependency-error rendering regression; and an expanded pinned-Lean
CLI smoke that checks a guard importing a deliberately ill-typed dependency in an
isolated temporary repository. Existing cancellation and dependency restoration
regressions remain covered.

Final gate: 252 Rust development tests, clippy with the documented baseline
allowances, and the expanded pinned-Lean CLI smoke pass.
