# mathmux implementation plan

> Status: implementation-ready v0 plan. This document is the source of truth for the first Unix
> implementation. Experimental documents describe evidence and carry no product contract.

## Product boundary

mathmux provides fast Lean checks and controlled Git integration for coding agents working in
isolated worktrees. It manages workspaces, local `main`, check certificates, submissions, and one
validation queue. Agents edit files and invoke mathmux from their current directory.

mathmux does not orchestrate agents, write proofs, choose dependencies, manage Lean toolchains, or
contact remote services.

## Command-line API

mathmux exposes five top-level verbs:

```text
mathmux ws create <name>
mathmux ws list
mathmux ws delete <name>
mathmux check [<file>]
mathmux sync
mathmux submit -m <message>
mathmux show <ref>
```

The current directory identifies the workspace for `check`, `sync`, and `submit`. Commands emit short,
token-efficient summaries. Details are available through `show`, which always requires a reference.
References use a bare type prefix and sequence number, such as `w12`, `c72`, `s18`, and `u31`.

### Workspaces

`ws create` creates a managed branch and isolated Git worktree. `ws list` reports compact state.
`ws delete` accepts one workspace and refuses deletion while it contains unsubmitted changes.

mathmux alone updates the local `main` branch. Agent worktrees never check out or mutate `main`.
Separate workspaces may edit and check the same repository-relative file concurrently. Their source
buffers, Lean processes, certificates, and Git state remain isolated.

The repository has a configurable workspace limit. The default reserves system and build memory,
then budgets 6 GiB for each workspace. A 32 GiB machine normally permits four workspaces; a 64 GiB
machine permits eight. `ws create` reports the limit when no slot remains.

Each checked workspace may retain one hot Lean worker bound to its most recent file and import
fingerprint. Switching to a file that needs a different import environment replaces that process.
Least-recently-used eviction is a safety valve for memory pressure. An idle timeout releases workers
during normal inactivity without deleting their workspaces.

### Check

`check <file>` synchronously certifies the requested Lean file and the source dependencies required to
elaborate it. It never checks reverse dependents. Bare `check` applies the same operation to every dirty
Lean file in dependency order. A successful command returns a check reference and stores its
certificate internally. Failed checks return diagnostics and create no certificate.

A certificate covers:

- the exact target content;
- every transitive project-source dependency;
- imported module artifacts;
- Lake configuration, Lean options, and the pinned toolchain; and
- the workspace identity and requested source version.

No background certification survives the command. An error in a completed command snapshot returns
immediately after mathmux triggers `SnapshotTask.cancelRec` for each unvisited subtree. A clean prefix
carries no success meaning, so successful checks wait for the complete file.

### Sync

`sync` brings the newest mathmux-managed `main` into the current worktree and returns an update
reference. A clean integration updates the workspace base. Conflicts remain in the agent worktree for
resolution. Any changed source, dependency, configuration, or artifact fingerprint invalidates the
affected certificates and Lean workers.

### Submit

`submit` accepts no check reference. It requires internal certificates that cover the exact current
dirty-file state and rejects missing or stale coverage. Under the repository integration lock it
creates the workspace commit, applies it to the newest local `main`, and publishes `main` atomically.
An integration conflict leaves `main` unchanged and directs the workspace to `sync`.

Acceptance returns a submission reference without running a build or axiom audit. The submission
record contains its commit, integration base, covered check references, and validation state.

### Show

`show <ref>` renders full details for workspaces, checks, submissions, sync operations, and validation
state. Unknown, malformed, and missing references are errors.

## Checker design

Use at most one supervised Lean helper process per hot workspace. The helper is built with
`Language.mkIncrementalProcessor (Language.Lean.process setup)` and runs the project's module system.
Each request supplies the exact source version and genuine edit. Success waits for the full snapshot
tree, then collects both reported and unreported messages from every snapshot. Normal kernel checking
remains enabled.

The helper reports parsed imports with its response. The daemon uses them to maintain a project import
graph and reverse edges. A native filesystem watcher monitors Lean sources, Lake configuration,
toolchain selection, and relevant build metadata. Filesystem metadata filters candidates; content
hashes decide validity.

Dirty dependencies build in topological order before their importers are checked. Any changed imported
artifact replaces the affected helper process. Lean import environments are never refreshed inside an
existing process because compacted imported regions remain resident and repeated extension loading is
unsupported. A safe Lake module build remains the fallback when recorded build commands cannot be
validated.

The first implementation ships no Lean plugin and no language-server backend. Direct processing won
the large-file latency comparison. LSP remains a possible low-memory backend after v0.

## Artifact sharing

Every worktree owns its `.lake/build` directory, traces, generated configuration, dependency graph,
and mutable package state. Writable build directories never cross workspace boundaries. Dependency
source checkouts may be shared only when immutable and keyed by the exact manifest.

All daemon-owned Lake invocations use:

```text
LAKE_ARTIFACT_CACHE=true
LAKE_CACHE_DIR=<stable toolchain cache>
LAKE_RESTORE_ARTIFACTS=false
```

Lake maps a complete module input hash to content-addressed, read-only outputs. Identical source,
imports, options, platform, and toolchain therefore compile once across worktrees. Cache hits resolve
shared `.olean`, `.olean.server`, `.olean.private`, `.ilean`, and native artifacts without copying all
outputs into the worktree.

The daemon coalesces concurrent dependency builds with the same input fingerprint. The direct checker
does not publish the edited target as a compiled artifact because serialization would increase check
latency. Dependency builds publish their outputs, and submission validation publishes the target for
later workspaces and revisions.

## Submission validation

One repository worker validates immutable accepted revisions. It uses a hidden clean build worktree
and the shared artifact cache. Validation performs a complete Lake build followed by one batched
artifact axiom audit over the exported deliverable roots.

The audit rejects `sorryAx`, undeclared custom axioms, and private generated axioms outside policy.
The initial allowlist contains `propext`, `Classical.choice`, and `Quot.sound`. Native evaluation is
reported as a separate compiler-trust classification.

An active validation always finishes. Pending descendant submissions coalesce to the newest revision,
and skipped submissions link to the later validation that contains them. mathmux never cancels an old
build. Accepted `main` may temporarily lead the newest validated revision; `show <submission>` exposes
that state.

## Daemon and persistence

Implement one native Rust binary containing the thin CLI and repository daemon. Unix support comes
first, using a Unix-domain socket, native file watching, advisory file locks, and supervised process
groups. IPC, paths, locking, watchers, and child-process control sit behind narrow platform traits for
future macOS and Windows implementations.

The daemon owns workspace metadata, short references, SQLite state, certificates, filesystem watches,
Lean workers, the integration lock, and the validation queue. Durable state lives under the Git common
directory. Git, Lake, and Lean run as child processes with argument arrays and a controlled environment.

The first command starts the daemon when the repository socket is unavailable. A startup lock prevents
duplicates. The daemon stays alive while clients, Lean workers, or validation work remain. After worker
idle eviction and an empty queue, a short grace period ends the daemon. SQLite and Git provide recovery
after a crash; incomplete operations reconcile before new mutations begin.

## Required verification

The implementation is ready when it passes these checks:

- multiple workspaces edit and check the same Lean file without interference;
- valid, invalid, repaired, rapid-superseding, and fail-fast source versions report correctly;
- dependency addition, removal, type change, and artifact rebuild invalidate the right workers;
- bare checks cover every dirty Lean file while avoiding reverse dependents;
- stale or incomplete certificates block submission;
- integration conflicts preserve local `main` and workspace changes;
- identical builds across worktrees hit one shared artifact entry;
- active validation finishes while queued descendants coalesce correctly;
- daemon restart recovers references, queue state, and managed workspaces; and
- workspace and worker limits hold under four concurrent agents, with an eight-agent stress run on a
  64 GiB host.

## Measured constraints

The selected direct checker used about 4.2 GiB RSS on a real 1,492-line Mathlib module and about
5.9 GiB on the larger generated fixture. LSP used about 2.0 GiB. Direct checks beat LSP by roughly
1.6 to 2.4 seconds on the real module; its tail edit completed in about 0.16 seconds versus 2.58
seconds. Local fail-fast errors returned in roughly 10 to 32 ms. Same-process dependency refresh added
about 7 GiB per attempt and later returned stale results, which requires process replacement.
