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
```

Development issues and telemetry use SQLite. Set `MATHMUX_ISSUE_DB` to choose
the database; `mathmux status` shows repository state.
