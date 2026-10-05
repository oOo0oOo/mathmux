# mathmux

Mathmux manages Git workspaces for Lean projects, searches declarations, checks
changes, and integrates submissions into local `main`.

## Install

```sh
cargo install --locked --force --git https://github.com/oOo0oOo/mathmux mathmux
```

## Use

For a clean Lean repository at `~/proofs` with local `main` checked out:

```sh
cd ~/proofs
mathmux ws create my-work
cd ../.mathmux-proofs/my-work
```

Edit your Lean files in the new workspace, then:

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

`mathmux sync` brings changes from local `main` into your workspace.
`mathmux sync --push` publishes local `main` to its configured remote.

## Search and probe

Search by name, concept, type, or source text; inspect a file’s declarations
and imports:

```sh
mathmux search "Nat.add*"
mathmux search "compact continuous"
mathmux search "type:Nat → Nat"
mathmux search Proof.lean dossier
```

Probe signatures, source, and usages; inspect goals and failed checks; try Lean
terms or tactics in context:

```sh
mathmux probe Nat.add_comm signature
mathmux probe Nat.add_comm usages
mathmux probe cREF evidence
mathmux probe Proof.lean:12 "by simp"
```

Replace `Proof.lean:12` with your file and line, and `cREF` with a failed check’s
reference. Probes do not edit files or replace checks.

Use `mathmux --help` or `mathmux COMMAND --help` for command details.
