# Mathmux experiment

## Question

Mathmux needs a fast way for coding agents to check one dirty Lean file inside an ordinary Lake
project. This experiment compares five Lean interaction families behind the same check contract.

The primary criterion is warm time to complete diagnostics. Aggregate memory under concurrent work
is second. Every result must be fresh and complete.

## Scope

The experiment covers the file-checking operation used inside agent workspaces. Each agent edits its
own file using normal tools and asks Mathmux to check it against the current project state.

Integration validation remains a separate clean `lake build` on the integrated main revision. The
file checker should prepare only the target and its imports.

## Check contract

Every candidate must:

- check the current source contents with the project's pinned Lean toolchain and Lake configuration;
- use current direct and transitive dependencies;
- return diagnostics for the exact requested source version;
- report completion only after the whole target file has been processed;
- recover after an invalid edit is repaired;
- supersede stale work when a newer check arrives;
- avoid building modules downstream of the target; and
- distinguish target errors, dependency errors, cancellation, timeout, and internal failure.

`lake setup-file` is the common project-context primitive. It prepares imports and returns a
`ModuleSetup` before the competing check operation.

## Candidates

1. `Language.Lean.process` with `mkIncrementalProcessor` and retained snapshots. Test retained
   `Language.Lean.processCommands` as a variant.
2. `IO.processCommandsIncrementally` with retained `IncrementalState`.
3. The Lean language server. Test standard versioned diagnostics and a custom endpoint that waits for
   the current snapshot and returns complete diagnostics.
4. Fresh Lean processes using `--setup`, `--incr-header-save`, `--incr-save`, and `--incr-load`.
5. Short-lived checkers restored from persisted `CompactedRegion` state.

A targeted Lake module build with a shared artifact cache is the simple baseline.

## Fixture

Create one small Mathlib project:

```text
MathmuxFixture/
  Shared.lean
  Worker1.lean
  Worker2.lean
  Worker3.lean
  Worker4.lean
  Downstream.lean
```

`Shared.lean` contains common definitions and imports. The four worker files import it and contain
similarly sized, independent proofs. Each should be about 30 to 60 lines and exercise ordinary
elaboration with small tactics. A fragment of Rowland's prime-generating recurrence may be used if
useful; its full theorem is outside the experiment.

`Downstream.lean` imports the worker files and serves only as a downstream-build sentinel.

Each concurrent worker receives an isolated workspace and checks a different worker file:

| Concurrency | Targets |
| --- | --- |
| 1 | `Worker1.lean` |
| 2 | `Worker1.lean`, `Worker2.lean` |
| 4 | `Worker1.lean` through `Worker4.lean` |

## Checks

Each worker performs three fixed checks:

1. Check the valid file.
2. Apply one local edit that causes a type error and check again.
3. Repair the edit and check once more.

The test consists entirely of these three fixed source states. Equivalent edits are placed at the same
relative position in every worker file.

Run two additional correctness probes once per candidate:

- change `Shared.lean` in one workspace and confirm the target uses the changed dependency;
- submit two target versions in quick succession and confirm only the newer version completes.

## Procedure

1. Pin the Lean toolchain, Mathlib revision, fixture revision, machine configuration, and resource
   limits.
2. Put every candidate behind the same minimal `prepare`, `check`, `cancel`, and `shutdown` harness.
3. Establish the expected diagnostics with a fresh ordinary Lean check.
4. Run the contract checks and remove incorrect candidates from the performance comparison.
5. Measure cold preparation once, then run the valid, error, and repair checks with warm retained state.
6. Repeat the warm checks at concurrency 1, 2, and 4. Start concurrent checks from a common barrier.
7. Randomize candidate order. Run enough repetitions for stable medians; extend the run only when two
   candidates are close.

## Measurements

Record:

- cold preparation time;
- warm time to complete current-version diagnostics;
- diagnostic correctness;
- peak aggregate process-tree RSS;
- idle resident memory;
- aggregate throughput at concurrency 1, 2, and 4;
- cancellation latency; and
- recovery behavior after the error and dependency probes.

Completion requires diagnostics for the whole current source version. Early goals, progress
notifications, and partial diagnostics remain supplementary measurements.

## Selection

Disqualify a candidate that returns stale diagnostics, misses the changed dependency, completes before
the whole file is checked, or builds `Downstream.lean` during a normal target check.

Choose the remaining candidate with the lowest warm complete-check latency across the 1, 2, and 4
worker cases. Use aggregate memory, cold preparation, cancellation, recovery, and implementation
complexity to decide close results. A second backend is worthwhile only if it provides a clear memory
or process-isolation advantage.

## Existing evidence

The sibling repository `../lean-interact-bench` contains the source survey, prototypes, and earlier
measurements. The most useful starting points are:

- `BENCHMARK.md`
- `RESULTS.md`
- `PRIMITIVES.md`
- `results/summary.csv`
- `results/support.csv`

Those measurements identify promising implementations. This experiment supplies the common contract,
fixture, and concurrent workload needed to select Mathmux's backend.
