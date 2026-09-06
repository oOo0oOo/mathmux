# Generic proof-context delivery: implementation checklist

This is the agreed scope. Workspace synchronization, remote failure snapshots,
and dependency-preparation dashboards were explicitly excluded by the operator.
The development release is gated on completing this list and verifying the final
installed build. The earlier 697322f build is interim.

- [x] Structured search/probe resolution, returned counts, backwards compatibility,
  and correction of legacy empty-result classification; preserve historical rows.
- [x] Complete typed failure categories and telemetry regression coverage.
- [x] Failure bundles: focused actual/expected differences, import-aware ranking,
  at most three relevant laws, one usage, explicit unverified/applicable distinction.
- [x] Assumption inspection: preserve premises, expose selected input structures,
  distinguish proof assumptions/data inputs, inspect constructors/definition body.
- [x] Construction and counterevidence discovery: direct negative-existence
  statements, hypotheses retained, source versus verified evidence distinguished,
  snapshot invalidation, compact early discovery notices.
- [x] Project-authored obstruction/replacement/example links, with no inferred
  mathematical replacement or automatic proof of equivalence.
- [x] Intended-application experiments: explicit Lean context, actual elaboration,
  remaining goals, relevant obligation APIs, no source edits/certificates.
- [x] Small-case selection: retrieve bounded existing constructions and examples,
  explain remaining premises, provide explicit-context inspection/experiment paths.
- [x] Definition sensitivity: syntactically absent inputs and explicit reductions;
  never claim semantic independence from syntactic absence.
- [x] Complete documentation/help digest and tests across unrelated fixtures;
  real Lean and CLI smoke; replay the known coercion episode without project rules.
- [ ] Land final verified changes on main, then request Agent Two's development
  release, verify the installed build, and deliver concise guidance to the swarm.

Validation before final release: 237 Rust development tests; 15 real Lean service
cases; isolated real CLI coverage of inspection, application, evidence caching and
source-change invalidation, authored routes/examples, telemetry counts and explicit
provenance. Source and compiled declaration duplication has regression coverage
for issue i140. The earlier coercion episode retrieves the two actual repair laws
within its top three candidates using generic signature rules.

Telemetry includes explicit optional actor/session provenance; causal follow-ups
require qREF/cREF rather than inferring causality from shared-workspace adjacency.
Evidence freshness is explicitly scoped to project sources/imports and pinned
configuration, not verification of externally modified dependency artifacts.
