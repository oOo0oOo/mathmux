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

Development builds print a retained telemetry `eREF` for failed daemon responses,
including probe infrastructure failures. Attach it with
`mathmux issue report SUMMARY --ref eREF`; an infrastructure timeout does not
produce a Lean result or a certificate.
