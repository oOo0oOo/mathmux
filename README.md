# mathmux

## Install and start

From a clean Lean repository on local `main`:

```sh
cargo install --locked --force --git https://github.com/oOo0oOo/mathmux mathmux
mathmux ws create <name>
cd <workspace-path>
# spawn an agent in this workspace
mathmux --help
```

`mathmux ws create` prints the workspace path. The spawned agent's first
command should be `mathmux --help`. Repeat this for each parallel workspace.

## What mathmux manages

- Git workspaces and project progress via `ws`, `status`, `sync`, and `submit`
- Lean interaction via `check` and `probe`
- Source search via `search`

## mathmux won't

- orchestrate or run agents
- generate or modify proofs
- manage toolchains or dependencies
- access remote resources

## Development

```sh
cargo build --release --features development
cargo install --locked --force --features development --path .
python tests/cli_contract_smoke.py /path/to/mathmux /path/to/pinned/lean
python tests/lean_probe_smoke.py /path/to/project-toolchain/bin/lean
python tests/synthetic_sorry_smoke.py /path/to/mathmux /path/to/project-toolchain/bin/lean
python tests/axiom_audit_smoke.py /path/to/project-toolchain/bin/lean
```

Development issues and telemetry use SQLite. Set `MATHMUX_ISSUE_DB` to choose
the database; `mathmux status` shows repository state.

`mathmux status` includes the current validation phase and latest build output.
To resume a timed-out validation of the latest submission, use
`mathmux dev revalidate sREF`, then `mathmux status`. Completed build artifacts
are reused, and the full build and transitive axiom audit run again. Superseded
submissions cannot be retried.

Cold dependency preparation has a separate cancellable fifteen-minute budget;
target Lean elaboration remains limited to five minutes, and short probes retain
their existing total deadlines. A dependency-preparation timeout can likewise be
resumed by repeating the same `mathmux check` command. For a larger cold graph,
use `mathmux check FILE --setup-timeout 3600` (seconds, 1–86400). This changes
only dependency preparation; target elaboration and short probes keep their limits.
During preparation, the
check streams elapsed time and the latest Lake task every ten seconds;
`mathmux show cREF` also retains its current phase. Unchanged direct imports
can still require a rebuild when sync changes a transitive dependency.

A focused source check elaborates in a reusable Lean worker; it does not emit
that source's `.olean` artifact. A subsequent importing guard may therefore
compile the source during dependency preparation, even immediately after a
passing source check. Setup manifests are also specific to each target file.
Lake's `Replayed` jobs reuse cached outputs and diagnostics; they are not fresh
compilations. The transitive dependency count is not a count of rebuilt modules.

The imported-constant audit supersedes older audit results. The daemon queues
the latest previously passed revision for fresh validation when necessary;
historical results are marked obsolete until covered by a current audit.

New checks retain Lean informational messages, including `#print axioms`, in
`mathmux show cREF --all`. Cached checks carry forward retained messages; output
discarded by older versions cannot be recovered from their saved references.
For type mismatches, `mathmux probe cREF types` and `evidence` include saved
`pp.all` detail with explicit universe and instance arguments.

`mathmux show sREF --wait` waits up to 600 seconds by default. For a long queue,
use `mathmux show sREF --wait --wait-timeout 3600` (seconds, up to 86400).
A wait timeout ends only the watcher; the check or validation continues.
Build progress retains the latest Lake task across linter messages.

Type-mismatch check responses point directly to `mathmux probe cREF types`.
That view highlights the first type difference, including retained expanded
instance/universe detail when available. `mathmux show cREF --all` continues
to expose the complete original diagnostics and informational messages.

An exact-name miss may include the requested signature or source for a unique
indexed namespace alternative, verified against its current source. It remains
explicitly a suggestion, not an exact hit or a Lean certificate. Ambiguous,
unmerged, stale, and still-indexing results are not automatically selected.

Development telemetry assigns each CLI invocation an attempt ID, shared with
the daemon and retained across transport retries. Distinct reads of the same
reference (including compact and `--all`) are recorded separately. Internal
operations on the request thread carry its parent attempt ID. Optional
`MATHMUX_ACTOR_ID` and `MATHMUX_SESSION_ID` values provide attribution; response
character counts measure rendered summary text, not model tokens. Older clients
without attempt IDs retain legacy reference-based deduplication.

Status keeps registered workspaces visible after their recent activity expires.
Rows labeled `wREF` report MathMux activity (`active` or `quiet`), not external
agent liveness. Workspaces leave this list when deleted with `ws delete`.

A passed single-file `cREF` can supply a contextual probe's file even when the
check was cached and has no diagnostics. The probe reads the current source;
it does not certify that source or reinterpret the saved check. Multi-file
checks without a diagnostic require an explicit `FILE` or `FILE:LINE` choice.
Concurrent probes wait at most two seconds for a busy worker or worker startup
lock, then return actionable retry guidance. Active checks are left running;
probe execution deadlines are unchanged.
Contention returns `probe busy (not queued)` with the occupied source and guidance
to wait for the active request before continuing sequentially. Telemetry counts
these rejected requests as `busy`, separately from infrastructure failures.

Development builds print a retained telemetry `eREF` for failed daemon responses,
including probe infrastructure failures. Attach it with
`mathmux issue report SUMMARY --ref eREF`; an infrastructure timeout does not
produce a Lean result or a certificate.

During dependency preparation, status separates the latest Lake output from
active Lean source files observed under that setup process. This bounded Linux
process snapshot is best effort; unavailable activity is labeled explicitly.

Fresh focused checks warn when a newly elaborated public instance name also
appears in another compiled module indexed for that workspace. This bounded
check is advisory: the index can be incomplete or stale, and full joint-import
validation remains authoritative. Give local instances unique explicit names
to avoid generated-name collisions.

Selective submission rejects omitted project prerequisites whose workspace
source differs from managed main, before staging or integration. Include those
prerequisites, submit them first, or sync and recheck. Covered submissions show
the actual covering validation status and retain an unverified label when that
validation failed or its audit is obsolete. `show --wait --all` combines waiting
with expanded stored detail.

Development builds accept `mathmux show eREF` and `show eREF --all` to inspect
retained telemetry directly. Event records are already complete and do not
support `--wait`; they are diagnostic evidence, not proof certificates.

Focused checks reject synthetic `sorry` terms inserted by Lean's error recovery,
even when Lean suppresses the underlying error while re-elaborating section
variables. The diagnostic names the affected declaration and its location.
Ordinary explicit `sorry` remains a draft warning; imported guards and the full
transitive axiom audit still determine proof completeness. Older focused-check
certificates must be refreshed under this check behavior.

Search and probe `qREF` snapshots are retained for up to 48 hours and 50,000
results per repository. Historical packet references can therefore expire even
when associated check or submission references still resolve. Re-run the original
search or probe with its declaration or file context to obtain a fresh snapshot.
An unknown query-reference response does not establish that its declaration is absent.
