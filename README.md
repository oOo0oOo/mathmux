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
resumed by repeating the same `mathmux check` command.

The imported-constant audit supersedes older audit results. The daemon queues
the latest previously passed revision for fresh validation when necessary;
historical results are marked obsolete until covered by a current audit.

New checks retain Lean informational messages, including `#print axioms`, in
`mathmux show cREF --all`. Cached checks carry forward retained messages; output
discarded by older versions cannot be recovered from their saved references.
For type mismatches, `mathmux probe cREF types` and `evidence` include saved
`pp.all` detail with explicit universe and instance arguments.
