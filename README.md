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
cargo build --release --features development
```

The binary is written to `target/release/mathmux`.

To install that development build for the local fleet:

```sh
cargo install --locked --force --features development --path .
```

## Minimal CLI for fast local Lean checks in isolated git worktrees

### mathmux will do

- manage isolated git worktrees, commits, merges, and project progress
- check Lean files, build targets, and audit axioms

### Search and probe

`search` is the discovery and source-reading interface; `probe` inspects a known
declaration, exact Lean context, or stored failure. Both return a `qREF`, whose
full bounded result is available through `show qREF --all`.

```sh
mathmux search name:Nat.succ
mathmux search 'type:_ → _' --limit 12
mathmux search Mathlib/Data/Nat/Basic.lean dependents
mathmux probe Mathlib/Data/Nat/Basic.lean '#check Nat.succ'
mathmux probe Proof.lean:42 goal
mathmux probe Proof.lean:42 'by simp'
```

Run `mathmux search --help` and `mathmux probe --help` for the complete compact
grammar. Probe never guesses an elaboration context, and `check` remains the
certification step after source edits.

For source-only ranges of 48 lines or fewer, compact output already contains
the full requested range; use `--all` for longer ranges or broader result
detail.

### mathmux won't

- orchestrate or run agents
- generate or modify proofs
- manage toolchains or dependencies
- access remote resources

## Development

Probably won't accept your PR. Write an issue, I prefer my own agents.
