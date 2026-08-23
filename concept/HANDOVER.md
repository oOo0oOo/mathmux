# Mathmux handover

## Purpose

Mathmux is intended to give coding agents a small, fast command-line interface to Lean projects.
Its first responsibility is workspace management and file checking. It may later grow into a broader
interface for formal mathematics, informal mathematical material, and search.

The immediate task is an experiment. Five promising Lean interaction families should be evaluated
behind the same user-visible check contract before choosing the production foundation.

Speed is the primary decision criterion. Memory use is second. Correctness and freshness are hard
requirements rather than tradeoffs.

## Intended workflow

The eventual tool should support this lifecycle:

1. Create an isolated agent workspace from the current main branch.
2. Let the agent edit ordinary files with its normal tools.
3. Synchronize newer main changes into the workspace.
4. Check a selected Lean file as quickly as possible.
5. Submit the workspace changes for integration.
6. Run a separate clean full-project build for the newest integrated main revision.

The command names and exact public interface remain open. This experiment concerns the Lean interaction
behind the file-checking operation.

## Check contract

Every candidate must expose the same observable behavior:

- Accept a Lean source file in a potentially dirty workspace.
- Check the current source contents in the file's exact Lake project and pinned Lean toolchain context.
- Make stale direct and transitive dependencies available before checking the target.
- Build only the dependency closure required by the target.
- Avoid building modules that depend on the target.
- Avoid a full-project build.
- Return diagnostics tied to the exact checked source version.
- Report completion only when the current file's complete diagnostic result is known.
- Recover correctly after an invalid edit is fixed.
- Supersede or cancel stale work when a newer check arrives.
- Apply the project's Lean options, plugins, module identity, and import artifacts.
- Clearly distinguish dependency failure, target failure, cancellation, timeout, and internal failure.

`lake setup-file` is the common project-context primitive worth using across the experiment. It resolves
the target's imports, builds required import artifacts, and returns a `ModuleSetup`. It should be treated
as context preparation rather than as one of the competing checking primitives.

## Candidate families

### 1. Full Lean language snapshots

Evaluate `Language.Lean.process` with `Language.mkIncrementalProcessor` and retained full-file snapshots.
Also evaluate retained `Language.Lean.processCommands` snapshots as a distinct variant in this family.

This is Lean's underlying language-processing model. It covers the header and body, supports prefix and
intra-command reuse, exposes snapshot diagnostics, and carries cancellation tokens. The existing benchmark
measured a retained tail edit at about 41 ms with roughly 6.5 GiB peak tree RSS.
The smaller `processCommands` variant measured about 43 ms and may offer a simpler route to the same
latency.

### 2. Incremental frontend command processing

Evaluate `IO.processCommandsIncrementally` with retained `IncrementalState`.

This is the smaller batch-facing interface over Lean's incremental snapshot machinery. It directly
returns accumulated command messages and previously measured edit checks near 43 ms with roughly 6.5 GiB
peak tree RSS. The experiment should determine whether its simpler surface remains sufficient once exact
project setup, dependency changes, cancellation, and complete diagnostics are required.

### 3. Lean language server

Evaluate the standard Lean LSP using document open/change notifications and a current-version diagnostics
barrier.

Also evaluate a custom LSP or server-RPC endpoint that waits for the current snapshot and returns its
complete diagnostics directly. Existing custom handlers answered snapshot queries in about 40 to 42 ms;
the experiment must establish whether that speed holds for a complete-file freshness barrier.

This candidate represents Lean's supported editor-facing service. It already handles project setup,
incremental snapshots, dependency staleness, worker restart, diagnostics, progress, and cancellation. It
also leaves room for later goals, code actions, references, widgets, and search-related features.

The earlier benchmark's roughly 42 ms warm goal request is not a complete file check. This candidate must
be judged using the time until complete diagnostics for the current document version are known. Its
measured Mathlib worker footprint was roughly 8 to 9 GiB peak tree RSS.

### 4. Fresh Lean processes with persisted CLI snapshots

Evaluate `lean --setup` together with `--incr-header-save`, `--incr-save`, and `--incr-load`.

This candidate trades resident workers for process isolation and persisted reuse. The earlier benchmark
measured a full-prefix tail edit around 2.2 seconds with roughly 3.3 GiB peak tree RSS, while creating the
snapshot took about 15.7 seconds and produced an artifact around 316 MiB. It remains interesting as a
memory-oriented or crash-isolated approach and as a fallback when retaining a worker is undesirable.

### 5. Restored compacted state

Evaluate a short-lived checker restored from `CompactedRegion` state containing as much prepared import
and checking context as can be reused safely.

This candidate explores a middle ground between a large resident worker and a cold process. The earlier
benchmark restored small persisted regions in about 137 ms with roughly 88 MiB peak RSS. Those numbers do
not yet demonstrate a complete Mathlib file check, so state fidelity, practical artifact size, and scaling
to real projects are central questions for this family.

## Baselines and operating variants

Include a targeted Lake module build with a shared artifact cache as the simple build-system baseline. It
must target only the selected module and its dependency closure.

Also evaluate pools of persistent workers keyed by compatible import headers. Pooling is an operating
variant for the resident candidates rather than a separate Lean checking primitive. It matters because
the production workload will contain several independent agent workspaces.

## Required experiment cases

Use the same fixture, machine conditions, source versions, and correctness oracle for all compatible
candidates. At minimum, cover:

- Cold project and import startup.
- First complete check after startup.
- Repeating an unchanged check.
- Tail edit.
- Edit near the beginning of the file.
- Valid edit, invalid edit, then repair.
- Import-header change.
- Dirty direct dependency.
- Dirty transitive dependency.
- Changed file that is downstream of the target.
- Workspace synchronization that changes the target only.
- Workspace synchronization that changes an imported dependency.
- Workspace synchronization that changes only downstream modules.
- Slow elaboration superseded by a newer edit.
- Timeout followed by successful reuse or restart.
- Switching between two target files.
- Worker or process failure followed by recovery.
- One, four, and five agents checking concurrently.
- Concurrent agents using the same import header in separate workspaces.
- Concurrent agents using different import headers.
- Bursts where all agents submit edits together.
- Sustained mixed checks, edits, cancellations, and workspace synchronization under memory pressure.

The dirty-dependency cases must prove that the current dependency source was used. The downstream case
must prove that downstream modules were not built as a side effect.

## Measurements

Record these separately for every case:

- Context or setup time.
- Time to first useful diagnostic.
- Time to complete current-version diagnostics.
- Median, p95, failures, and timeouts.
- Peak process-tree RSS.
- Peak aggregate RSS across all workers and supporting processes.
- Resident idle memory.
- Per-agent latency, aggregate throughput, queueing delay, and fairness under concurrent load.
- Disk growth and persisted-state size.
- Amount of dependency work performed.
- Restart and recovery cost.
- Whether stale work was successfully cancelled.

Count a result as correct only when every diagnostic belongs to the requested source version and the
completion signal covers the whole target file. Early goals, progress messages, and partial diagnostics
may be measured as first signal, but they do not establish completion.

## Selection rule

Disqualify a candidate if it can return stale diagnostics, miss dirty dependency changes, build downstream
modules during a normal file check, or report success before complete diagnostics are known.

Among the remaining candidates, choose the one with the lowest warm complete-check latency across realistic
agent edits, including the five-agent workload. Use aggregate memory, cold-start cost, cancellation,
recovery, and implementation burden to break close results. A secondary backend or fallback is acceptable
when it serves a distinct memory or isolation mode.

## Separation from the main build

The agent-side check is deliberately narrower than integration validation. It answers whether one dirty
file is valid against its required dependencies. A clean main build separately runs the project's full
`lake build` and catches affected downstream modules.

Artifact sharing between the clean builder and agent workspaces is in scope for later optimization. It
must not weaken the clean-build guarantee or allow one dirty workspace to affect another workspace's
result.

## Existing evidence

The source survey, benchmark methodology, implementation probes, and raw result matrix live in the sibling
repository `../lean-interact-bench`. Start with:

- `BENCHMARK.md`
- `RESULTS.md`
- `PRIMITIVES.md`
- `notes/lean4-core-primitives.md`
- `notes/lean4-tactic-state-and-cancellation.md`
- `notes/lean4-server-rpc.md`
- `notes/lake-primitives.md`
- `notes/lsp-family.md`
- `experiments/incr-snapshot-benchmark.md`
- `experiments/hermetic-warm-attempt-loop.md`
- `results/summary.csv`
- `results/support.csv`

The previous measurements identify promising directions. They do not replace this experiment because some
rows used different fixture sizes or measured a useful early query rather than complete file diagnostics.

## Handover state

The repository begins with this concept only. No implementation language, internal architecture, process
model, protocol, storage layout, or command syntax has been selected. The next agent should make those
choices while preserving the shared check contract and fair five-family comparison above.
