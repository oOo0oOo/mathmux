# mathmux

**WIP: Not ready for use!**

## Install and start

1. Install the latest mathmux from source:

   ```sh
   cargo install --locked --force \
     --git https://github.com/oOo0oOo/mathmux mathmux
   ```

2. From a clean Lean repository on local `main`, create a workspace:

   ```sh
   mathmux ws create <name>
   ```

3. Start the agent in the workspace path printed by mathmux. Its first command should be:

   ```sh
   mathmux --help
   ```

Repeat step 2 for each parallel workspace.

## Development issue and telemetry storage

Development issue reports and telemetry use one SQLite database. An explicit
`MATHMUX_ISSUE_DB` path always wins. Otherwise MathMux uses
`$XDG_DATA_HOME/mathmux/development.sqlite3` (or `$HOME/.local/share` when
`XDG_DATA_HOME` is unset). If that managed path is unavailable because the
filesystem is read-only or denies access, repository commands fall back to
`<common-git-dir>/mathmux/global/development.sqlite3`. The fallback is
MathMux-owned repository state and survives daemon restarts; it is not an Oli
storage path. Commands run outside a repository still require a writable
default path or an explicit `MATHMUX_ISSUE_DB`.

Deployments that sandbox agents must expose the repository's `.git/mathmux`
directory as a writable persistent path, or set `MATHMUX_ISSUE_DB` to another
writable MathMux-owned location. Do not point this variable at Oli's state or
data directories.

Inspect the managed main revision, validation queue, workspace changes, latest
checks, and recent submissions at any time:

```sh
mathmux status
```

## Development build

Build mathmux directly from the local checkout:

```sh
cargo build --release --features development
```

The binary is written to `target/release/mathmux`.

To install that development build for the local fleet:

```sh
cargo install --locked --force --features development --path .
```

After installing a new binary, any normal MathMux command can replace an older
per-repository daemon automatically. To explicitly restart only that daemon,
run this from an assigned workspace:

```sh
mathmux restart
```

This drains active MathMux work and starts a fresh repository-local daemon. It
does not restart `oli-dev.service`, reset Oli setup, or drop agent sessions.

Inspect and manually reclaim MathMux-owned generated storage from any managed
workspace:

```sh
mathmux dev storage
mathmux dev gc --dry-run
mathmux dev gc
```

Normal GC removes setup files belonging to deleted workspaces, shared setup
files no active workspace references, and obsolete Lean-service generations.
It also enforces the 48-hour/50,000-row search-history cap and the
30-day/100,000-row development-telemetry cap, then passively checkpoints the
SQLite databases. It does not remove submissions, checks, source history,
active worktree `.lake` directories, the shared Lake artifact cache, or the
validation worktree. It reports Git worktrees outside the MathMux registry,
including dirty or missing paths, but never removes them. GC is manual; MathMux
does not schedule it or trigger it from free-disk thresholds.

For an explicitly confirmed deep cleanup, inspect the candidates first:

```sh
mathmux dev gc --hard --dry-run
mathmux dev gc --hard --confirm
```

Hard GC requires idle checks, validation, and integration. It removes only
single-link Lake artifacts, generated validation `.lake/build` output, `target/`
directories from clean, unlocked, process-free unregistered Cargo worktrees,
and clean unregistered worktrees whose tree exactly matches managed `main`.
Dirty, locked, divergent, active, or outside-parent worktrees are preserved and
reported; divergent worktrees may still have their generated `target/` removed.
The command never removes source, package dependencies, submissions, or the
shared Lake output cache.

To intentionally discard a dirty workspace and any unsubmitted branch commits,
an operator may use `mathmux ws delete --force NAME`. The normal delete command
remains refuse-by-default and never discards workspace changes.

## Minimal CLI for fast local Lean checks in isolated git worktrees

### mathmux will do

- manage isolated git worktrees, commits, merges, and project progress
- check Lean files, build targets, and audit axioms

### Search and probe

`search` is the discovery and source-reading interface; `probe` inspects a known
declaration, exact Lean context, or stored failure. Both return a `qREF` for
stored result sets, while exact declaration results point directly to a focused
probe command.

Identifier-shaped searches resolve exact names first and fail closed on a miss,
with at most three near-name suggestions. Use the explicit `declaration NAME*`
form for wildcard name discovery. Exact output stays compact:
signature, path, import availability, and a usage count. Use `probe NAME source`,
`probe NAME outline`, or `probe NAME usages` for focused detail. Regex and literal
source matches group by enclosing declaration, and the reusable `qREF` is printed
last. Refine grouped searches before using `show qREF --all`.

```sh
mathmux search Nat.succ
mathmux probe Nat.succ signature
mathmux probe Nat.succ source
mathmux probe Nat.succ outline
mathmux probe q123#2 outline
mathmux probe q123#2 find simp
mathmux search 'type:_ → _'
mathmux search Mathlib/Data/Nat/Basic.lean dependents
mathmux probe Mathlib/Data/Nat/Basic.lean '#check Nat.succ'
mathmux probe Proof.lean:42 goal
mathmux probe Proof.lean:42 'by simp'
mathmux show c123 --wait
```

If a check is still running, use `mathmux show c123 --wait` before probing its
stored goal or analyses.

For asynchronous submission validation, use `mathmux show s123 --wait` to wait
for the queued or running validation before inspecting its final result.

Run `mathmux search --help` and `mathmux probe --help` for the complete compact
grammar. Probe never guesses an elaboration context, and `check` remains the
certification step after source edits.

For source-only ranges of 48 lines or fewer, compact output already contains
the full requested range. Longer ranges name the next non-overlapping range.

### mathmux won't

- orchestrate or run agents
- generate or modify proofs
- manage toolchains or dependencies
- access remote resources

## Development

Probably won't accept your PR. Write an issue, I prefer my own agents.

### Inspecting mathematical contracts (probe-v5)

Before building on an unfamiliar API, inspect what it assumes and whether a
construction or obstruction has been found:

```sh
mathmux probe Some.Namespace.Data assumptions
mathmux probe Some.Namespace.Data evidence
mathmux probe Some.Namespace.Data examples
mathmux probe Proof.lean:42 Some.Namespace.Data evidence
mathmux probe Proof.lean:42 '#inspect Some.Namespace.theorem'
mathmux probe Proof.lean:42 '#apply proposedLemma'
mathmux probe c123 context
```

`assumptions` retains the indexed signature and points to selected input APIs.
`evidence` returns bounded source candidates for constructions, negative-existence
results, and related laws, with their hypotheses. A constructor may still need
impossible inputs. A missing search result is not an existence verdict, and a
source candidate is not a verified obstruction. The positioned `evidence` form
runs Lean inspection of one negative-existence candidate in the specified context;
it reports the actual elaborated statement and axiom dependencies, including
`sorryAx`. Verify the exact specialization and every premise before using it.

`#inspect` distinguishes proof assumptions from data inputs, shows constructors
or one definition body, and reports parameters syntactically absent from that
body. This is not a semantic independence test. Use explicit small cases with
`#check (TERM : EXPECTED_TYPE)`, `#reduce TERM`, or `by TACTIC`. `#apply` runs an
application experiment and shows remaining obligations; it does not edit source
or issue a check certificate. All these Lean experiments require explicit context.

`cREF context` keeps the original failure and retrieves up to three related laws
and one indexed usage. Candidates are ranked using type/signature overlap and
small application or coercion laws, not claimed to solve the goal. Normal checks
only add a compact pointer to this opt-in inspection, avoiding extra Lean work.

Development telemetry now includes structured resolution/count/failure metadata
for search and probe responses. Older response formats remain readable. Historical
text-derived outcome labels are preserved and may misclassify empty searches;
compare new-build episodes separately. Result counts are returned records, not
proofs of usefulness. Unclassified failures remain unclassified rather than being
assumed to be infrastructure defects.

The isolated Lean smoke suite is run with
`python tests/lean_probe_smoke.py /path/to/project-toolchain/bin/lean`.

`probe NAME examples` selects at most three existing small constructions or
project-authored examples, with signatures and remaining inputs. Ranking by
indexed input count is only a starting point; implicit typeclass requirements
still need the positioned `#inspect` / `#check` experiment.

Failure context includes a focused actual/expected difference and import-aware
candidate availability when the workspace import graph is ready. Unknown import
availability remains unknown. Candidates have not been tested against your goal.

Projects can optionally provide `.mathmux-evidence.json`:

```json
{"version":1,"links":[{"subject":"Demo.Contract","obstruction":"Demo.noContract",
"replacement":"Demo.WeakerContract","examples":["Demo.smallExample"],
"explanation":"This route preserves only the weaker contract."}]}
```

Routes are project-authored suggestions, never inferred equivalences. The file is
bounded to 64 KiB and 256 links. Exact discovery shows a compact relevant notice.
Positioned evidence inspection caches only direct negative-existence declarations
with standard Lean axioms (no `sorryAx` or custom axioms). Notices require matching
project source, transitive project imports, and toolchain/Lake configuration.
This is a project snapshot check, not revalidation of externally modified package
artifacts. The complete inspected premises and specialization remain in the probe
reference; no global impossibility is inferred from a specialized theorem.

Development callers may explicitly set `MATHMUX_ACTOR_ID` and
`MATHMUX_SESSION_ID` (up to 128 non-control characters) for durable provenance in
telemetry requests. Missing identities remain unknown; MathMux does not guess
agent identities from workspace ownership. New follow-up associations require an
explicit `qREF`/`cREF` in a probe or show request. Adjacent commands in a shared
workspace do not establish causality. Historical telemetry is retained unchanged.

Run the isolated CLI integration suite with
`python tests/cli_contract_smoke.py /path/to/mathmux /path/to/pinned/lean`.
It owns only its temporary repository and daemon.
