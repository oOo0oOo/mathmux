# Workflow-level error prevention

The target is earlier correction of mistaken proof routes, not a growing command surface. Changes should be judged against complete episodes and the evidence available at each decision, including unsuccessful candidate applications.

## Current evidence

Two recorded, workspace-filtered episodes end at submissions s3978 and s4017. The second recording covers the late instance-mismatch segment, not the full task. Together they contain 95 calls: 36 searches, 13 probes, 41 checks, three show calls and two submissions. There are 35 failed checks: 11 rewrite mismatches, 10 type mismatches, seven remaining-goal reports, five stalled simplifications, one failed application and one instance-inference problem. These are diagnostic categories, not independent mathematical mistakes.

All 13 probes inspected global names/source/signatures; neither recording used a positioned applicability experiment or a check-context probe. The repeated Fourier failures concern bundled/function coercions and scalar actions. The manifold episode ultimately aligns topology and chart instances. Thus finding a plausibly named theorem was often insufficient: its representation and instance choices needed to fit the actual goal.

Evidence: telemetry 151766–151877 and 153075–153125; local audit snapshots `/tmp/mm-completed-episode-151766-151877.json` and `/tmp/mm-instance-episode-153075-153125.json`. Counts can be reconstructed from request verbs and response success flags. Different builds and tasks prevent interpreting these counts as a before/after experiment.

## Priorities

1. **Expose applicability obstacles in the path agents already use.** Preserve the actual goal, differing types/instances, missing premises and distinction between a retrieved candidate and an elaborated application. Evaluate whether existing bounded check-context evidence can replace repeated unproductive edits; extra hint lines alone have not established uptake.
2. **Make successful results trustworthy.** A completed proof, an admitted proof, unresolved metavariables and a theorem with strong local assumptions must remain distinguishable. Kernel acceptance is not a mathematical adequacy verdict. Keep the existing provenance, admission and unused-input checks in the regression set.
3. **Make discovery uncertainty accurate and recoverable.** Separate index misses, generated declarations, wrong scopes and actual mismatches. Preserve substring/Unicode correctness while measuring latency. Do not recover speed by reinstating false negatives.

These priorities are generic across Lean projects. No theorem names, mathematical domains or retained formalization workspaces should become product assumptions.

## Next experiment

Use the existing isolated Box/coercion replay and negative retrieval control to evaluate an earlier, bounded presentation of check-context evidence. Compare the normal failed-check output with the current `probe cREF context` output and the corrected check. Require that the useful conversion is supported by an indexed signature, retain its premises/import constraints, and retain the explicit unverified label. Include a control with no applicable conversion and a control with incidental name/body overlap. Do not add automatic proof-search or a new verb merely to make this demonstration pass.

Success means evidence needed for the next correct experiment becomes visible earlier without hiding the goal, asserting applicability, or materially inflating routine output. A subsequent comparable fleet episode is needed to assess fewer failed attempts; a passing fixture alone cannot prove a productivity gain.

## Secondary finding

An isolated `by simp?` probe returned only `solved`, while Lean itself emitted `simp only [and_self]`. Successful informational messages are discarded in the local-probe path. This is a real information-loss candidate, but none of the latest 1,500 inspected probe requests used the surveyed suggestion tactics. Retain it behind demonstrated applicability friction rather than expanding low-use functionality first.

## Operating discipline

Batch observation around completed episodes and meaningful release outcomes. Avoid frequent status polling, cosmetic release churn and speculative special cases. Keep deeper evidence recoverable; compact defaults should remove repetition, not uncertainty or proof obligations.

## Controlled applicability experiment (installed 2f3993f)

Three isolated workflows were exercised using the existing commands:

- Positive conversion: the initial failed check was 415 characters; a separate 624-character context probe exposed `convert_coe` with an explicit unverified label. Rewriting through that law made the next check pass.
- Incidental overlap: a theorem with related words only in its name/documentation did not become a conversion candidate. The context response was 480 characters.
- Unmet premise: a candidate requiring `False` remained unverified and showed that premise in its signature. Positioned `#inspect` reported `proof assumption required: False` and an elaborated implication type, despite having no global axioms. This distinguishes global trust from applicability under local assumptions.

Replays: `/tmp/mm-workflow-positive.py`, `/tmp/mm-workflow-negative.py`, `/tmp/mm-workflow-premise.py`. All completed successfully outside formalization workspaces. These controlled cases establish available evidence and useful controls, not measured fleet productivity.

The next implementation candidate is to reuse one compact conversion candidate in an already-detected repeated rewrite failure, rather than requiring another context command. Preserve the goal and the complete candidate signature/premises, label applicability and import uncertainty, and omit the automatic candidate when those facts cannot fit the budget. Reuse the existing retrieval path; do not parse its rendered prose or run automatic proof search. The first ordinary failure and failures without a supported candidate should remain concise. Validate the three workflows again against the actual default check output before release.

The repeated-failure delivery candidate is implemented in i103. The existing detector requires three non-cache-only failures with a matching blocker; the implementation does not introduce another repetition threshold. Indexed retrieval is shared with full context output, and automatic rendering never truncates the selected signature to fit. Positive, negative and unmet-premise replays pass; the positive workflow is retained in the regular CLI smoke. The remaining evaluation is comparable fleet usage after deployment, including whether this prevents another unproductive edit and whether retrieval latency is proportionate.
