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

Inspect the managed main revision, validation queue, workspace changes, latest
checks, and recent submissions at any time:

```sh
mathmux status
```

## Development build

Build mathmux directly from the local checkout:

```sh
cargo build --release
```

The binary is written to `target/release/mathmux`.

## Minimal CLI for fast local Lean checks in isolated git worktrees

### mathmux will do

- manage isolated git worktrees, commits, merges, and project progress
- check Lean files, build targets, and audit axioms

### mathmux might eventually do

- local search, like lean-lsp-mcp
- informal mathematics (getting inspired by [TheoremGraph](https://arxiv.org/abs/2606.25363))

### mathmux won't

- orchestrate or run agents
- generate or modify proofs
- manage toolchains or dependencies
- access remote resources

## Development

Probably won't accept your PR. Write an issue, I prefer my own agents.
