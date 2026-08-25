# mathmux

> Status: pre-implementation. The interface is designed and the experiment harness remains available.

mathmux is a minimal native CLI for fast local Lean checks in isolated Git worktrees. It manages
workspaces, synchronous check certificates, local integration, and one asynchronous build and axiom
validation queue.

The [implementation plan](PLAN.md) is the current source of truth. The completed experiment harnesses,
fixtures, and results remain available at the `experiments-final` Git tag.

## Scope

- manage isolated git worktrees, commits, and merges
- check dirty Lean files with exact dependency state
- share Lake artifacts across worktrees
- validate accepted submissions with a build and axiom audit

Possible later work includes local search inspired by `lean-lsp-mcp` and informal-mathematics tools
inspired by [TheoremGraph](https://arxiv.org/abs/2606.25363).

mathmux stays outside agent orchestration, proof generation, toolchain and dependency management, and
remote services.

## Planned CLI

```text
mathmux ws create|list|delete
mathmux check [<file>]
mathmux sync
mathmux submit -m <message>
mathmux show <ref>
```

## Development

Probably won't accept your PR. Write an issue, I prefer my own agents.
