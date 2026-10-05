# mathmux

Mathmux supports parallel agent work through a local CLI for Git management,
code search, and efficient Lean interaction.

Use `mathmux --help` for an overview and `mathmux COMMAND --help` for details.

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

`mathmux show sREF --wait` waits for submission validation.

`mathmux sync` brings changes from local `main` into your workspace.
`mathmux sync --push` publishes local `main` to its configured remote.

## Search

Find declarations by name, concept, or type; read and search source.

```sh
mathmux search Nat.add_comm
mathmux search "Nat.add*"
mathmux search "compact continuous"
mathmux search "type:Nat → Nat"
mathmux search Proof.lean:10-25
mathmux search Proof.lean dossier
mathmux search Proof.lean dependents
mathmux search Proof.lean "/sorry|admit/"
```

## Probe

Inspect declarations, goals, and failures; try Lean terms and tactics in context.

```sh
mathmux probe Nat.add_comm signature
mathmux probe Nat.add_comm source
mathmux probe Nat.add_comm usages
mathmux probe Fin fields
mathmux probe Proof.lean:12 goal
mathmux probe cREF evidence
mathmux probe Proof.lean "#check Nat.add_comm"
mathmux probe Proof.lean:12 "by simp"
```

Probes do not edit files or replace checks.
