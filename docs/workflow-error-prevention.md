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


## Dependency availability at the failing check (i104)

Two later workflows failed on files absent from their workspace, then located the dependency and synced before passing (telemetry 153304–153309 and 153348–153353). These are environment-availability failures, not evidence of invalid mathematical statements. Existing source lookup already explained managed-main availability, but check output required agents to discover that separately.

An isolated registered-library replay reproduces the Lake missing-file diagnostic, the source lookup handoff, and a passing check after sync. Check output now offers that recovery only for an exact project dependency path absent from both workspace disk and workspace HEAD, present on main disk and committed in main HEAD. Missing-everywhere, uncommitted, unrelated, and locally deleted files do not receive the hint. Original diagnostics remain intact; no sync runs automatically. The regular CLI smoke covers uncommitted/committed availability and successful recovery.

The preceding local-estimate episode contains nine searches, six probes, four checks, one sync and one submission (workspace-filtered telemetry 153315–153358). It does not exercise repeated rewrite failures, so it cannot establish i103's effect on productivity.


## Assumptions in compact inspection (i105)

A real positioned inspection (telemetry 153395) hid the explicit ellipticity premise and the result behind 44 omitted lines. The agent recovered them with `show --all` (153400). A generic conditional theorem with twelve data parameters and 35 ambient types reproduced the same omission of `required : False`; global `axioms: none` was still visible. This is a valid conditional theorem, not a detected contradiction. Its applicability condition should be visible at the decision point.

Long inspection previews now prioritize trust status, the result and proof assumptions ahead of routine inputs and duplicated elaborated-type text. Multiline fields stay attached, with explicit continuation markers and a total assumption-field count when the budget cannot show everything. Short inspections and full stored details retain their existing presentation. This presentation change does not remove the Lean service's existing per-field text limit; a long elaborated type can still require source inspection. The CLI regression checks both the visible False premise and recovery of the omitted ambient inputs.


## Retaining elaborated contract evidence (i106)

The full response in telemetry 153400 was already cut by the Lean service at 800 characters per contract field. `show --all` could not recover that missing evidence. A generic theorem assuming and returning a conjunction of sixty `True` propositions followed by `TerminalRequirement` reproduced the loss: the terminal requirement disappeared from every stored contract field.

Contract types, including local inputs, constructor types and negative-existence subjects, now retain the text rendered by Lean. The normal preview owns the display budget; definition bodies retain their explicit one-step bound. This removes MathMux's extra contract-text cut, not Lean's own pretty-printer elision or inference limitations. In the controlled replay the default response was 551 characters, while the full response retained all three occurrences of the terminal requirement in 18,273 characters. Storing a requested long contract uses more space; compact output does not require discarding its evidence.

The pinned Lean service's 39 cases pass, and the CLI regression checks retained requirements and bounded default output. This supersedes the service-limit caveat in the i105 section above.


## Instance search and applicability labels (i107)

A completed mixed-error proof recovered by annotating an intermediate bundled derivative and its coercion (c54586–c54588 and indexed final source). A generic `Lifted Nat Box` instance with a `Box`-to-`Nat` coercion reproduces the mistake without a timeout: an expected `Nat` result asks Lean for `Lifted Nat Nat`, while annotating the intermediate `Box` makes the application pass.

Existing type search retrieves the useful alternative, so another instance-search mechanism is not justified. However, the exact query `type:Lifted Nat Nat` also returned `Lifted Nat Box` as an unlabeled structural candidate. The scoring code admits related structural rows after the Lean applicability stage; this is not solely a warming behavior. Type-search output now labels candidates lacking verified applicability as related and unverified, retaining the existing `applicable` label for verified matches. Ranking and ordinary search output are unchanged. The help digest is search-v13.

Tests cover both labels and ordinary output. The CLI replay compares exact and relaxed discovery with failing/successful synthesis and a successful explicitly typed application. Negative discovery has limited index coverage in the isolated fixture and is not a nonexistence proof. A subsequent failed-instance handoff should use existing retrieval and preserve this distinction.
