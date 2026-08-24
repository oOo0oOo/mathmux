# Mathmux experiment results

## Recommendation

Use the standard Lean language server with `textDocument/waitForDiagnostics` as Mathmux's dirty-file
checker. Keep one server session per active workspace and use Lake's `setup-file` result for module
artifacts. The custom complete-diagnostics endpoint had equivalent latency and correctness, so the
built-in barrier wins on implementation cost.

Use a clean targeted Lake build for integration validation. A second dirty-file backend does not add
enough value: short-lived snapshot checkers saved about 5 GiB at four workers, while checks took about
9.2 seconds instead of 45 milliseconds.

The file-switching follow-up supports keeping recently visited files open in that single LSP session.
With four files visited in rotation, the first visit to each file was cold and the next two reused its
worker. LSP completed the twelve visits in 27.8 seconds versus 44.5 seconds for fresh Lean with cached
per-file `ModuleSetup` artifacts. The LSP retained 14.8 GiB after opening all four files; the fresh
process strategy retained no idle memory.

## Result

Five repetitions of valid, error, and repair checks produced 465 raw rows. Times below are medians in
milliseconds. RSS is the peak aggregate process tree in MiB.

| Backend | Workers | Valid | Error | Repair | Wall | Peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| LSP standard | 1 | 17.6 | 38.3 | 37.8 | 50.2 | 4,627 |
| LSP standard | 2 | 19.9 | 43.8 | 45.1 | 52.0 | 9,864 |
| LSP standard | 4 | 23.4 | 51.2 | 53.4 | 61.3 | 20,328 |
| LSP custom | 1 | 16.8 | 38.3 | 36.3 | 49.4 | 4,617 |
| LSP custom | 2 | 19.7 | 42.4 | 45.6 | 51.7 | 9,854 |
| LSP custom | 4 | 23.8 | 47.0 | 46.2 | 61.8 | 20,331 |
| CLI snapshot | 1 | 7,936 | 8,526 | 8,443 | 8,468 | 3,922 |
| CLI snapshot | 2 | 8,281 | 8,499 | 8,312 | 8,578 | 7,621 |
| CLI snapshot | 4 | 8,992 | 9,011 | 9,260 | 9,353 | 15,126 |
| Lake build | 1 | 4,230 | 6,777 | 6,787 | 6,775 | 3,958 |
| Lake build | 2 | 4,232 | 6,787 | 6,806 | 6,841 | 7,782 |
| Lake build | 4 | 3,891 | 6,419 | 6,462 | 6,567 | 15,521 |

## File-switching follow-up

One workspace was visited in the order Worker1 through Worker4 three times. The rounds applied a
valid source, an error edit, and its repair, producing four cold opens and eight revisits. Three
repetitions produced 216 correct checks. Times are milliseconds; total is the median sum of twelve
sequential visits.

| Strategy | Cold visit | Revisit | 12-visit total | Observed RSS | Idle RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| LSP, keep files open | 6,821 | 43 | 27,801 | 14,832 | 14,832 |
| Fresh Lean, cache setup per file | 6,556 | 2,282 | 44,547 | 2,915 | 0 |
| Fresh Lean, recreate setup | 6,564 | n/a | 78,602 | 2,915 | 0 |
| Lake targeted build | 6,839 | 6,832 | 81,895 | 3,939 | 0 |
| LSP, close after each visit | 6,887 | n/a | 82,561 | 5,235 | n/a |
| CLI snapshot per file | 14,548 | 8,401 | 123,477 | 4,131 | 0 |

At the measured per-visit medians, fresh Lean with cached setup overtakes keep-open LSP only when
about 89% of visits are first-time file opens. Closing each LSP document after a switch removes its
latency advantage. The retained file workers, rather than the protocol alone, account for the fast
revisits.

Observed RSS is the largest sampled check-process tree. `setup-file` time is included in cold visits,
while its transient RSS is outside this follow-up's sampler. The LSP close policy's post-close idle
RSS was not sampled.

LSP idle RSS was 4.55 GiB for one worker, 9.78 GiB for two, and 20.24 GiB for four. CLI snapshots and
Lake builds had no idle process. Median cold preparation was 11.7 to 11.9 seconds for LSP, 14.3 to
14.5 seconds for CLI snapshots, and 4.2 seconds for the targeted Lake baseline.

## Correctness gate

The fresh ordinary-Lean oracle returned zero, one, and zero errors for valid, error, and repair. Both
LSP paths, CLI snapshots, and Lake builds matched it across the matrix. A valid change to `Shared.lean`
caused target errors for each surviving backend, and no target check built `Downstream.lean`.

Rapid versions 201 and 202 yielded diagnostics only for version 202 in both LSP paths, completing in
38.7 and 40.1 milliseconds. Short-lived CLI and Lake work were terminated in about 2 milliseconds;
the replacement valid checks then succeeded.

The retained `Language.Lean.process` and `Language.Lean.processCommands` prototypes missed all five
local error edits under this module-system fixture. `IO.processCommandsIncrementally` matched the
three source states, then failed the contract because its harness lacked an in-flight cancellation
boundary. Persisting the prepared `Environment` with `CompactedRegion` exceeded the 30-second setup
limit, reached 10.15 GiB RSS, and produced no artifact. These candidates stopped after concurrency 1.

## Reproduction

The run used Lean 4.34.0-rc2, Mathlib `f2916a54665af851fc9a4da901cfc242c47a8922`, fixture commit
`38a1cb3844d25847b671412826c6f9e0ae89445b`, 24 logical cores, and 128,725 MiB RAM. The fixture uses
Lean's module system throughout, with `requiresModuleSystem := true` and explicit public/exposed API.

Run `./experiment.py --repetitions 5`. Machine metadata and disqualifications are in
`results/run.json`; summaries are in `results/summary.json`; contract probes are in
`results/contract.json`; per-check data are in `results/raw.csv` and `results/raw.jsonl`.

Run `./switch_experiment.py --repetitions 3` for the file-switching follow-up. Its metadata, summary,
and per-visit measurements use the `switching_` prefix in `results/`.
