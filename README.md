# mathmux

Mathmux manages Git workspaces for Lean projects, searches declarations, checks
changes, and integrates submissions into local `main`.

## Install

```sh
cargo install --locked --force --git https://github.com/oOo0oOo/mathmux mathmux
```

## Use

From a clean Lean repository with local `main` checked out:

```sh
mathmux ws create my-work
cd <workspace-path>
```

Use the workspace path printed by `ws create`. Edit your Lean files there, then:

```sh
mathmux check
mathmux submit -m "Describe the change"
mathmux status
```

`check` checks changed Lean files. `submit` requires passing checks, integrates
changes into local `main`, and queues a build and axiom audit. Validation can
pass with `sorry` declarations; these are reported separately.

To wait for validation, use `mathmux show sREF --wait`, replacing `sREF` with the
submission reference printed by `submit`.

- `mathmux search QUERY` finds declarations and source.
- `mathmux probe NAME` inspects a known declaration.
- `mathmux sync` brings changes from local `main` into your workspace.
- `mathmux sync --push` publishes local `main` to its configured remote.

Use `mathmux --help` or `mathmux COMMAND --help` for command details.
