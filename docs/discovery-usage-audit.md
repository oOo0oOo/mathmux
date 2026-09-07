# Discovery usage audit: probe-v6 through probe-v9

2026-09-07. The operator requested repeated hands-on rounds focused on preventing
formalization mistakes early. MathMux issues belong in MathMux's tracker and are
fixed by the tooling agent; Oli is reserved for runtime issues.

The test project was Atiyah–Singer, in dedicated managed workspace w67. Its source
was not edited or submitted. Development replay used separate state, search indexes,
and caches through `examples/discovery_replay.rs`; it did not replace the fleet daemon.
The implementation contains no project-specific names or mathematical routes.

| Usage evidence | Gap | Implemented correction |
|---|---|---|
| e147097 | An assumptions request was recorded as signature | Classify all current facets and #inspect/#apply; preserve old rows (i3) |
| q293180, q293182 | Headline theorem hides the analytic-comparison premise in a truncated signature | Show conclusion and explicit binders before implicit context; choose input type heads rather than arbitrary tokens (i4) |
| q293179; first replay | Projections and maps out of the requested type masquerade as construction examples | Exclude field rows and outer arrows/equivalences; preserve actual requirements in selectable qREF#N examples (i5) |
| q293181, q293183, q293193 | Broad discovery misses a point-case Subsingleton instance that Lean synthesis finds | Reserve targeted negative-existence/IsEmpty/Subsingleton candidates; explicit two-term property queries return matching source evidence, retaining specialization (i6) |
| q293225; third replay | A function requiring the impossible product-data contract has no warning at discovery | One compact source-evidence notice for an explicit input type; never infer failure at all specializations |
| q293237 | Failed application repeats context and hides the type comparison | Focused actual/required difference; full Lean diagnostic remains behind the reference (i7) |
| q293192; isolated replay | Empty warming index looks like evidence of absence | Explicit incomplete-index verdict and structured index_warming outcome, counted as partial rather than a completed miss (i8) |

Additional quality checks reject claims about a type inferred from an obstruction
to a wrapper or function space containing it. Obstruction verification tries at
most three candidates, stopping at trusted evidence; no additional attempt starts
after thirty seconds. An admitted first candidate no longer masks a subsequent
axiom-clean theorem. Each individual Lean call retains the existing timeout.

The third replay surfaced the known point-case singleton result first and flagged
the specialized product obstruction on the function requiring that data. Its six
warm source queries took 11–96 ms locally. This is not a cold-start benchmark:
initial indexing took about fourteen seconds, and an isolated uncached Lean setup
hit the existing 45-second dependency-preparation limit. The corresponding live
Lean probes succeeded. No toolchain-installation claim follows from that timeout.

Validation: 242 Rust development tests; clippy with the two documented baseline
lint categories allowed; full real CLI smoke including admitted-candidate fallback,
selectable examples, compact failed application plus full stored diagnostic,
evidence invalidation, and telemetry. The unchanged Lean service also retains its
previous 15-case smoke coverage. Counterexamples and parser regressions use generic
Demo/Data/Nat fixtures, including nested and Unicode binders.

Replay is a maintainer helper, not a proving-agent workflow. Pass an isolated
workspace and a scratch directory outside its source and live repository state;
feed lines beginning with search or probe on stdin. Never replay experimental
Lean work against an actively edited worker workspace.

A fifth replay of the original type-plus-subsingleton query returned the known
point-case instance first. Explicit property queries now omit unrelated results.


## Source usage round: probe-v7 (MathMux i9)

Actual fleet source requests e147282/q293279 and e147256/q293259 were reproduced
as q293282 and q293283 in the audit workspace. The long bundle-hom definition
stopped halfway through its return type without notice. `mfderiv` showed only the
first line of a multiline ambient variable command and then included the next
declaration's documentation. Nearby `extChartAt` and `contMDiffAt_iff` requests
confirmed that this was a general source-extraction defect.

Explicit source probes now reread the selected declaration from its current file,
retain the textual snapshot under a new reference, and display a contiguous
48-line/8,000-character preview. Lines are never silently shortened. Omitted source
has an exact continuation range and `show qREF --all`, which preserves the entire
stored source including long lines. Re-probing an old reference reads current
source under a new reference; the old snapshot remains unchanged. Indexed fallbacks
are labeled as excerpts, and unavailable source is explicit.

Ambient variable continuations survive comments and blank lines. Section scopes,
local variable/open commands, and the declaration's own documentation are retained;
neighboring docs, examples, attributes, and scope commands are excluded from its
body. Textual context is not represented as elaborated dependencies: irrelevant
ambient variables may be present, and omitted earlier ambient commands are labeled.
This remains a lexical reader, not a replacement for positioned Lean inspection.

Isolated replay q43/q45/q47/q49 (scratch state, not fleet references) recovered the
missing manifold binders and replaced neighboring docs with the requested docs.
The long definition offered continuation at file line 255, reaching the actual
bundle-hom result without guessing that a `letI` assignment ended the signature.
Warm requests took 29–117 ms. A subsequent replay verified comment-separated
binders as well. An initially warming dependency index was allowed to finish;
its early absence results were not treated as mathematical evidence.

Generic regression fixtures cover multiline/comment-separated variables, public
sections, local-scope cleanup, neighboring commands, Unicode lines, continuation
coordinates, and a source body larger than the former 16,000-character index cap.
The real CLI smoke checks the proof's last line and immutable old snapshots after
an edit. No mathematical source was changed. The search index version advances
once so existing cached source entries acquire the parser correction.

Release gate: 245 Rust development tests, clippy with documented baseline allowances,
and the expanded pinned-Lean CLI smoke all pass.


## Source navigation round: probe-v8 (MathMux i10)

Following the source snapshot with `find ContinuousLinearBundleHom` exposed another
concrete error: isolated q58 reported lines 298 and 368, counting twelve synthetic
ambient-context lines as file lines. The direct name-based find returned no body
matches because it searched only the old preview. The corresponding outline
contained only the declaration header.

Both direct and reference-based source/outline/find now refresh the complete
current textual snapshot. Find subtracts synthetic context from file coordinates,
labels ambient matches without inventing a file location, and reports empty or
capped literal-match results explicitly. Declaration-header detection shares the
source parser, including public declarations and attributes. Unavailable or indexed
fallbacks keep an explicit completeness limitation.

Replay q61/q63 returned the actual file lines 286 and 356 in both forms; the new
outline reached the return type at line 286 and later proof structure. Warm requests
took 34–130 ms. Generic tests cover ambient coordinates, attributed public headers,
no-match/capped-match responses, and direct/reference find plus outline beyond the
48-line preview. The expanded pinned-Lean CLI smoke passes. No formalization source
was changed. The previous probe-v7 development release was independently verified
before this follow-up was landed.


## Four further usage rounds: probe-v9 (MathMux i11–i14)

The next sample used recent fleet source requests e147368/q293331,
e147366/q293329, and e147499/q293425, plus nearby declaration forms in their
source modules. All replays used the isolated audit workspace and scratch state.

- **Bare variable commands (i11).** `HasMFDerivAt.comp` and
  `ContMDiff.mdifferentiable` still lost their fundamental manifold binders because
  the command was written as `variable` on its own line. The parser now collects
  the following binders, including comments and whitespace, and keeps such a command
  out of the preceding declaration body.
- **Preceding attributes (i12).** `writtenInExtChartAt_model_space` dropped its
  `@[simp, mfld_simps]` line. Source now includes preceding attributes and reports
  their actual starting line. Find and outline use that same start, preserving
  coordinates. This also fixes an old documentation test that attached a nested
  `to_additive` docstring to the original multiplicative theorem. Source enrichment
  recognizes an exact canonical name when compiled locations point past attributes.
- **Alias generators (i13).** `HasFDerivAt.hasMFDerivAt` reported unavailable source,
  although its alias command explicitly names it. Source now recovers the matching
  generator and points to its referenced declaration for premises. It does not
  fabricate an elaborated proof or signature. Exact generated names and namespaces
  are checked; unknown aliases retain the unavailable-source response.
- **Nonrec declarations (i14).** A nearby replay of
  `UniqueMDiffWithinAt.mono_nhds` exposed an unsupported `nonrec` modifier. It is now
  parsed normally, retaining its source and separating it from its predecessor.

The corrected warm replay recovered the alias generator (scratch q96), all missing
manifold binders, and the simplifier attributes. Its seven requests took 8–44 ms.
The nonrec replay also recovered the actual theorem body. Cold index warming was
allowed to finish before assessing results; the source index advances once for
this batch. No formalization source was edited or submitted.

Generic regression fixtures cover bare variable commands, attributes and source
coordinates, nested generated documentation, qualified/multiline aliases, false
alias matches, and nonrec boundaries. The CLI fixture now puts attributes above a
long proof and uses a standalone variable command; direct and reference-based
find/outline still locate the exact final proof line after the preview limit.


## Heavy usage campaign: source and early evidence (i15–i20)

Three passes used the dedicated audit workspace without editing formalization
source: 30 live CLI queries, 22 follow-ups, then one elaborated project-context
inspection and 32 isolated replays of the changed Searcher. The replay index was
still partially warming: successful fresh source reads are useful evidence;
missing candidates and example rankings are not exhaustive search conclusions.
Local transcripts: `/tmp/mm-heavy-1.jsonl`, `/tmp/mm-heavy-2.jsonl`,
`/tmp/mm-heavy-final-replay.out`, `/tmp/mm-heavy-round3.out`, `/tmp/mm-heavy-last.out`.

- i15: live q294176/q294196 resolved ambient type variable `E` as a global
  declaration, surfacing unrelated `EquivLike.subsingleton_dom` evidence.
  Bound signature/ambient identifiers now suppress that global lookup. The same
  real source queries no longer show the false warning; known concrete input
  obstruction evidence remains covered by an integration test.
- i16: exact `search ... source` omitted an alias generator and silently cut a
  long declaration, although `probe ... source` handled both. Both now use fresh,
  bounded source snapshots with explicit continuation and lossless stored detail.
  The replay recovered `Bornology.IsBounded.exists_norm_le` and reported the 311
  omitted lines of the long bundle-map declaration, with its next actual range.
- i17: live q294209 suggested three transformations needing existing Schwartz
  maps. Automatic examples now prefer candidates without direct subject inputs
  and label selected candidates that require one. This is a lexical ranking,
  not proof of independence: aliases, hidden prerequisites, and project-authored
  selections still need inspection. The repeated query labels both remaining
  direct-input candidates; generic fixtures verify ordering and labels.
- i18: a dependency-file Lean experiment previously returned infrastructure
  failure. It now explains the unavailable context and asks for a project file
  importing the API. Following that route in the actual project produced q294236,
  with elaborated premises and axioms for `SchwartzMap.norm_le_seminorm`.
  Symlinked dependency paths receive the same classification.
- i19: replaying `SchwartzMap fields` during indexing falsely called it a
  non-structure. Unknown indexed kinds now retain uncertainty and a source
  follow-up; warming output asks for a retry. A database integration fixture
  distinguishes unknown kind from a known non-structure.
- i20: the next constructor lookup had a near-name suggestion and therefore
  incorrectly claimed exact absence during warming. Suggestions no longer change
  that verdict or trigger premature name-repair instructions. Both empty and
  nonempty suggestion cases have regression coverage.

The final source/static replay took 0–171 ms per query; these timings exclude
initial indexing and do not establish full-fleet latency. The pinned-Lean CLI
fixture also verifies that explicit source search retains the final proof line
beyond its preview. No new grammar or project-specific logic was added.


## Follow the next step: constructor and generated-source handoffs (i21–i23)

Ten more live requests followed source, assumptions, examples, constructors and
Lean inspection in the audit workspace (`/tmp/mm-next-usage.jsonl`).

- i21: `SchwartzMap constructors` (q294266) returned a constructor name/path with
  no signature. Such results now point to the structure's fields and a positioned
  Lean inspection of its constructor. The tool does not invent an indexed type.
- i22: elaborated inspection printed long internal hygienic names for instance
  inputs. Lean's own expression printer now renders input references, including
  structured evidence premises and syntactically unused parameters. Instance data
  and instance propositions have distinct labels. A pinned-Lean regression checks
  both roles without internal `_hyg` or `._@.` names.
- i23: the alias-source follow-up for `Bornology.IsBounded.exists_norm_le` reached
  `isBounded_iff_forall_norm_le` (q294273), whose proof is generated by `to_additive`.
  Explicitly named simple generator attributes now recover original textual
  context with a prominent generator/original distinction and a Lean inspection
  route. Original source is never presented as the transformed proof or signature.
  Ambiguous namespace cases, inferred target names and unsupported attribute forms
  remain unavailable. Follow-up names containing apostrophes are shell-quoted.

Six isolated replays recovered the alias → explicit generator → original source
chain and checked neighboring source reads. Scratch constructor/field misses
were still warming and are not evidence of absence; constructor fallback output
has a focused Rust regression and is checked again after installation. All fixes
apply to generic Lean/Mathlib usage; no formalization files were edited.


## Example usability across module boundaries (i24)

The live workflow q294341 → q294342 → q294343 → q294344 selected the first
SchwartzMap example, inspected its premises, found an importing module, and ran
`#check` there. Lean rejected `AtiyahSinger.unitPeriodPoissonOutput`: it is private.
The assumptions dossier also incorrectly listed `[private]` as implicit context.

Automatic example ranking now prefers public candidates; authored selections keep
priority and selected private candidates receive explicit source/public-API
follow-up guidance. Visibility is displayed separately from Lean binders. Metadata
is stripped before result classification, including private constants with no
explicit arguments. Generic integration coverage verifies ordering, private
warnings, preserved real inputs, and concrete input obstruction evidence.

Four isolated replays (`/tmp/mm-round5-replay.out`) confirmed that the SchwartzMap
result begins with public candidates and that its private implementation has a
visibility line instead of a fake premise. These public candidates still require
existing Schwartz maps, which remains explicitly labeled; this is not an initial
construction claim. No formalization source was edited.

The replacement first candidate also passed a real positioned Lean `#check`
(q294348), confirming its function type in its project context.


## Inherited fields and constructor contracts (i25–i27)

Ten source/field/example requests followed the previous input-API guidance
(`/tmp/mm-round6.jsonl`). ContinuousLinearMap, LinearIsometryEquiv and Homeomorph
field dossiers (q294372/q294375/q294378) showed only locally declared fields,
without mentioning inherited linear-map/equivalence obligations.

- i25: field inventories now label omitted inherited obligations, show the
  indexed `extends` types and offer a positioned constructor inspection. A generic
  integration fixture covers a child with direct fields and a child with only an
  inherited parent. Non-inheriting inventories retain their compact form.
- i26: following the constructor route revealed q294383: inspecting bare
  ContinuousLinearMap.mk tried to synthesize its default continuity proof and
  failed. Explicit `@ContinuousLinearMap.mk` succeeded (q294384). Bare identifiers
  in inspection now elaborate with implicit application disabled before defaults
  can fire; applied expressions retain normal elaboration. Generic Lean coverage
  includes a constructor-like function with a default proof parameter.
- i27: the successful workaround still dropped the constructor's main inputs
  behind twelve implicit binders. Inspection now orders explicit inputs first and
  retains every input in stored detail. The UI keeps its compact budget and
  `show qREF --all` expansion. The full type remains after the inputs. Syntactically
  unused-parameter inspection likewise examines every parameter.

The changed service replay q196 succeeded on the originally failing bare query
and immediately displayed `toLinearMap` and the continuity proof obligation.
Five replay requests also checked the surrounding field route; dependency field
results still warming in the scratch index are not used as absence evidence.
A pinned-Lean fixture with thirteen implicit type parameters verifies the final
parameter survives and the explicit value comes first. No formalization edit or
submission was made.


## Audit workspace retirement and independent CLI coverage

The operator retired w67 and reserved w49/w50/w66 for formalization work. Tooling
smoke work now stays outside those workspaces. Installed product 67c7ae5 was
verified with a temporary CLI fixture covering inherited-only structures, a
constructor with a default proof, explicit-first inspection and retrieval of the
thirteenth implicit input through `show qREF --all`. This supplements the direct
Lean tests and replaces the planned live-workspace post-install replay. The
installed binary SHA-256 was
`f2932d9fdee07ca7dd3e7dfd5b2054f1425a82e11f324a63b1b1a805f7752426`.
The expanded CLI smoke passed without touching a formalization workspace.


## Exact-miss follow-ups must make progress (i28)

Read-only telemetry review found event 148808 / q294292 from the orchestrator:
`search eLpNorm_two` failed, then recommended exactly `search eLpNorm_two`.
No retained formalization workspace was entered to investigate this case.

A no-suggestion unqualified miss now offers a shell-quoted `NAME*` pattern.
Qualified misses first try their leaf; explicit declaration-kind forms extract
the actual name rather than suggesting the kind keyword. Root-qualified and
apostrophe-bearing names have regression coverage. Existing near-name and
index-warming behavior is retained.

In an isolated repository, the completed replay was: exact `eLpNorm_two` miss →
suggested `eLpNorm_two*` → a longer fixture declaration found. A qualified missing
name progressed through its leaf and pattern, then stopped with no results.
`/tmp/mm-round7-warm-replay.out` records this six-request warm replay. The earlier
cold replay was not used as evidence of absence. These are navigation checks,
not a claim that the fixture theorem exists in Mathlib.


## Fresh swarm evidence: attribute signatures and missing lexical context (i29–i30)

Read-only telemetry events 148939 / q294400 and 148944–148945 / q294405–q294406
revealed two remaining correctness faults. No retained formalization workspace
was entered for this investigation.

- i29: `OpenPartialHomeomorph.trans` had indexed signature
  `] protected def trans : OpenPartialHomeomorph X Z`. The parser searched header
  text for the name and found it inside `@[trans]`. It now slices from the regex's
  captured declaration-name byte position, accounting for indentation. Regression
  cases cover attributes, protected declarations, indentation and Unicode names.
  The index version advances to discard previously corrupted signatures.
- i30: ContDiffOn/ContDiffAt exact results had no stored source body. Automatic
  input evidence consequently treated their local `E` as a global declaration and
  surfaced an unrelated subsingleton theorem. Unqualified heads now require source
  context without an ambient-omission marker before global lookup. Qualified
  concrete input notices remain available. The generic integration fixture proves
  missing/truncated context suppresses the warning while qualified evidence survives.

Five isolated source/signature replays (`/tmp/mm-round9-replay.out`) recovered
correct signatures while retaining their attributes in source. The installed-CLI
smoke fixture now includes a theorem whose name matches its simplifier attribute.
The expanded CLI suite, 259 Rust tests and baseline clippy passed. These checks
use temporary repositories and do not alter formalization source.


## Complete multiline declarations without bodies (i31–i32)

Telemetry q294407/q294411 exposed an IsManifold signature ending after its first
line. Read-only inspection of the shared dependency source confirmed that this
class has multiline parameters and an inherited HasGroupoid requirement, with no
`where` token. No retained formalization workspace was entered or used for smoke.

- i31: header parsing now retains the whole declaration when there is no body
  delimiter, stopping at constructor alternatives and deriving clauses. Comments
  do not terminate a header. Regressions include multiline classes, structures,
  axioms, inductives and a comment containing `where`.
- i32: the replay exposed a generated-parent-projection hint appended directly to
  the type signature. That hint now belongs to documentation. Signatures and
  inherited-parent types contain declaration syntax, not tool-generated prose.
  Existing fallback tests verify that the documentation hint remains available.

The recorded dependency header was copied into an isolated textual replay:
`signature` now includes I/n/M, `fields` identifies HasGroupoid, and `source`
retains the complete header (`/tmp/mm-round10-replay-final.out`). This source-only
fixture is not a Lean adequacy check. The generic installed-CLI fixture separately
uses a valid multiline inherited-only structure and checks clean signatures.
260 Rust tests, baseline clippy and the expanded pinned-Lean CLI smoke pass.
Index version 12 invalidates previously truncated headers and contaminated types.


## Hom-space evidence is not evidence about its domain (i33)

Telemetry 148991/q294445 suggested `IsTerminal.subsingleton_to` as evidence
about an input type. Its actual conclusion is `Subsingleton (I ⟶ A)`:
a statement about a hom-space, not the object I. The current build reproduced
this independently with a Lean-checked generic function-space fixture and
`probe Demo.Data evidence`.

The source classifier now treats the top-level hom arrow like the existing
function arrow. Such conclusions remain related laws rather than direct
construction, emptiness, or subsingleton candidates for their domains. Nested
hom-space parameters still permit direct evidence about the outer type.
The focused contract suite covers all four classifications; isolated CLI smoke
checks that the misleading candidate disappears and its original source stays
available. No source-index or help grammar change is needed.


## Accurate consumer scope in usage dossiers (i34)

Telemetry 149014/q294467 and 149020/q294469 show dependency-only usages followed
by a `project consumers` summary. The dossier draws from all indexed scopes;
its label now says `indexed consumers`. Names are deduplicated before the
two-consumer budget, with `_root_.` normalized for identity and self-reference
filtering. Individual usage paths continue to show their origin.

This is a display correction; no indexing or query semantics changed. The
existing 15 probe tests pass. The earlier source-only fixture did not produce
compiled usage records, so it is not claimed as an end-to-end usage replay.


## Repeated inspection retains import-header context (i35)

Telemetry 149035/q294482 inspected an imported declaration at line 1; the
identical query 149036/q294483 then lost its elaboration context. Isolated
installed-CLI replay and direct Lean-service replay reproduced the transition
on unchanged source. Three inspections of `Nat.add` at an import header went
from success to two context failures.

Lean's incremental processor retains the header info tree in the processed
header state while omitting it from reused snapshot metadata. Context lookup
now falls back to that retained tree using the requested source range. It does
not substitute the file's final environment or restart/re-elaborate the file.
Three identical inspections now succeed. A local declaration defined after the
header remains unavailable there, and the existing out-of-range test still
fails. The direct Lean suite now covers 22 cases; CLI smoke also repeats the
import-header inspection three times. All work uses isolated temporary fixtures.


## Source-match handoffs use executable locations (i36)

Telemetry 149060/q294509 recommended probing the display label `source match
at …:2` as a declaration. An isolated regex search reproduced the hint and its
invalid-focus failure. Searching a line before the first declaration exposed a
second fabricated subject, `source`, in the next outline hint.

Source groups now point to `search FILE:LINE`; location results point to
`search FILE outline`. Paths use the existing shell-argument quoting. Replay
completed regex match → source location → declaration outline. The CLI smoke
follows both emitted commands through the real parser and checks the final
declaration, rather than merely checking hint wording.

An additional i35 neighbor audit shifted the import header by a comment and a
blank line between requests: initial and repeated inspections still succeeded.


## Authored source survives generated metadata (i37)

Telemetry 149055/q294505 reported current source unavailable for ContMDiffMap.
The saved hit had kind `generated`, while the source file contains an ordinary
`def ContMDiffMap`. Generated metadata is a compiled-index fallback category;
it does not prove the absence of an authored declaration.

Fresh source lookup now permits that category when the normalized, fully
qualified declaration name exactly matches the parsed source. A regression
first reproduced the rejection, then exercised a stored result → `probe source`
workflow against a real temporary source file. A generated name absent from
that same file still receives no invented source. All 114 search tests pass.
No source-index or help grammar change is required.


## Local instances are visible in source context (i38)

Telemetry 149136's source snapshot omitted a local Fact instance visible in
149138's file range. An isolated Lean fixture made the consequence concrete:
`local instance defaultSeven : Inhabited Nat := ⟨7⟩` changes a following
`def chosen : Nat := default` to 7, while the old snapshot showed only the def.

Source context now records local-instance declarations within their lexical
scope. Each preview is limited to four lines and 500 characters, with the
original source line and an explicit truncation marker when needed. Previews
are comments so source navigation cannot mistake them for the selected
declaration. The existing sixteen-command ambient budget still applies.
They disappear when their namespace or section ends.

The original replay now shows the value-bearing instance; `find` labels it as
ambient context. Regressions cover scope exit and long-body truncation, and the
CLI fixture checks the snapshot alongside Lean reduction to 7. All 115 search
tests pass. Index version 13 refreshes stored context; help is probe-v16.


## Generic compiled declarations retain a source handoff (i39)

Telemetry 149151/q294572 and 149167/q294582 returned an exact declaration name
and path without its signature or a next action. The stored kind was
`declaration`, the compiled index's generic fallback. That valid kind was absent
from the display's probeable-kind list.

It now receives the existing `probe NAME source` handoff. The exact-summary
regression reproduced the silent dead end with no signature or source, then
passed with the new hint. This adds no query syntax or unverified type claims.


## Exact source lookup respects root qualification (i40)

The signature-less result in telemetry 149177/q294591 led to an isolated replay
of the dependency source. After indexing completed, `Continuous.ae_eq_iff_eq`
was rejected while `_root_.Continuous.ae_eq_iff_eq` succeeded. The miss suggested
the original failing query. Source metadata existed but the SQL prefilter
excluded it before the canonical-name matcher could run.

Exact retrieval now canonicalizes the query before the full-text lookup and
admits either stored root spelling in the qualified SQL comparison. It retains
namespace restrictions. Regression cases cover both spellings in both
directions, unrelated namespaces, and a root-only query. All 116 search tests
pass. The actual source replay now completes search → signature → source with
its premises present, including on a cold index. The CLI fixture also exercises
both spelling directions. Existing indexes remain valid; no grammar change.


## Coverage notices agree with bounded concept aliases (i41)

Telemetry 149190/q294605 returned an injectivity result while reporting
`missing injection`. Controlled usage kept the desired result first, so there
was no evidence for changing ranking weights. A neighboring continuity query
reproduced the underlying inconsistency: search expands continuity to continuous,
but its coverage notice still required the original literal word.

Coverage now recognizes the same finite alias table used by query expansion,
with injection → injective added from the observed query. Alias evidence must
be a complete word/identifier segment; compact does not satisfy composition.
Cold and warm continuity/injection replays retain the desired result first
without false missing-concept warnings. An unrelated compact query still warns.
All 117 search tests pass. No new verbs or grammar are introduced.


## Signature requests stay on their API anchor (i42)

Telemetry 149216/q294623 used `search HasCompactSupport.of_compactSpace signature`
and received unrelated compactness declarations. A warm generic replay returned
both the named theorem and an unrelated theorem containing signature in its name.
The existing API-anchor parser treated signature as a refinement concept.

For the recognizable API anchors already handled by that parser, signature now
selects the exact lookup without refinement terms. No verb is added. Ordinary
`function signature` remains a concept query, and explicit type queries retain
their existing interpretation. Cold/warm replay returns one exact declaration;
a missing anchor produces its exact miss instead of signature-related results.
All 118 search tests pass, with a real CLI regression for the observed form.
Help is search-v9/probe-v16; existing indexes remain valid.


## Missing signature recovery (i43)

Telemetry 149235/q294653 and 149236/q294654 requested bare probes of known
APIs but received only names, paths, and usage counts. With no indexed signature,
the signature renderer removed the warming note and supplied no recovery route.
An isolated CLI replay with the observed missing-signature metadata reproduced
that dead end; the existing source probe recovered the authored definition.

A single unsigned signature result now explicitly says its signature is not
indexed and gives the existing `probe NAME source` command for textual context.
Complete signatures stay compact. This does not claim source is an elaborated
type or introduce new verbs, grammar, indexing, or a Lean process.
The focused regression fails on the old output; all 16 probe tests pass.
The fixed CLI replay follows that exact name-based source command successfully,
then verifies stored-reference source recovery. The real episode later used the
same source focus (149240–149241), supporting this handoff rather than a new API.


## Option context in source snapshots (i44)

Telemetry 149240/q294658 showed a source snapshot of a dependency declaration
preceded by `set_option backward.isDefEq.respectTransparency false in` and
`variable (F) in`. Only the variable command survived in its ambient context.
A standalone fixture accepted by pinned Lean reproduced missing persistent and
declaration-local options. This can obscure why copied source elaborates differently.

The existing ambient collector now retains top-level `set_option` commands using
its existing namespace/section and next-declaration scope handling. Indented
proof-local options are excluded from subsequent declaration context, as term-local
opens already are. Source remains explicitly textual, not an elaborated environment.
The same 16-command context budget applies; no verbs or grammar were added.

The regression failed before the fix. All 120 search tests pass; the standalone
replay retains the target option, removes it from the next declaration, and removes
namespace options after its end. CLI smoke covers the option-plus-variable chain.
Index version 14 refreshes cached source context; help is search-v9/probe-v17.
The expanded pinned-Lean CLI smoke and 8 help tests pass. Replaying the original
query against an isolated copy of TemperedDistribution.lean retains the option
only for its intended declaration, not the following apply lemma.


## Preserve mathematical notation in compact signatures (i45)

Telemetry 149262/q294680 displayed `f =ᵐ g` where the actual conclusion was
`f =ᵐ[μ] g`; μ was incorrectly counted as an implicit/typeclass binder. Replaying
the exact query against an isolated copy of LpSpace/Basic.lean reproduced the
corruption while the source probe retained the correct statement.

Compaction now considers only the leading outer binder sequence before the
result colon. Explicit argument types and conclusions retain their bracket/brace
notation. Mixed nested delimiters in actual context binders are balanced;
ambiguous input without the result colon is preserved rather than stripped.
Regression cases cover measure notation, continuous linear maps, set predicates,
subtype arguments/results, and nested subtype instances. The old formatter fails
the regression. Original-query replay now preserves μ and counts only the genuine
implicit binder. No verbs, grammar, index format, or help contract changed.
All 120 search tests pass. An isolated pinned-Lean CLI replay verifies a real
explicit subtype argument survives exact search. The prior installed release's
scoped-option context was independently checked successfully.


## Source ranges stop at actual declaration bodies (i46)

Telemetry 149292 queried Constructions.lean:481-510, starting at the documentation
for Homeomorph.ofEqSubtypes. Its result incorrectly said it started inside the
preceding continuousAt_subtype_val theorem. Original dependency-copy replay
reproduced this label and an inflated count of crossed declarations.

Source spans previously ran to the next declaration header. They now stop at the
complete textual body, excluding ambient preview lines from the length and keeping
the next-header boundary as a cap. Documentation/commands between declarations are
left unowned rather than attributed to the previous theorem. A range beginning in
a gap still reports the number of actual declarations crossed. Long proof bodies
are measured without the search-preview character cap.

The regression fails before the fix and covers docs, commands, ambient binders,
and a thousand-line proof. All 121 search tests pass. No verbs, grammar, stored
index format, or help contract changed.
Expanded pinned-Lean CLI smoke passes, including a documentation-start range.
Original-query replay reports seven crossed declarations without a false owner;
the neighboring 483-486 range still identifies Homeomorph.ofEqSubtypes correctly.


## API usage requests keep their intended target (i47)

Telemetry 149352/q294740 searched `exists_isSubordinate usages` and received
unrelated declarations plus a missing-usages coverage warning. A current generic
replay of `Demo.exists_target usages` returned unrelated_usages and a file-body
match, while `probe Demo.exists_target usages` stayed on the target.

Recognizable API usage requests in the existing exact text-search plan now route
to that existing probe dossier. Source-file searches and explicit type queries
retain their own plans. This adds no verbs or probe capability. The exact anchor
is resolved by the usual probe flow; missing or ambiguous names retain its usual
outcomes instead of becoming concept searches for usages.
Help is search-v10/probe-v17; indexes remain valid.
All 121 search tests, 8 help tests, and expanded pinned-Lean CLI smoke pass.
Generic cold/warm replay covers the target, missing target, ordinary concept, and
source-file find controls. Original-query replay against a copied dependency
returns the two actual exists_isSubordinate candidates with warming uncertainty,
instead of unrelated quadratic declarations; qualification remains necessary.


## Source find selectors do not create false matches (i48)

Telemetry 149377/q294756 searched a file for tsupport_sum using `FILE find TERM`
and returned comments containing “find a neighbourhood”. The parser treated find
as a literal OR term. Current copied-dependency replay reproduced both false lines.

An unquoted find immediately after the source target and before another term now
acts as the selector. A lone find, quoted find, and a later find term stay literal.
The requested terms otherwise retain their existing matching rules. The regression
fails on the old parser and covers each distinction. Help documents `[find] TERMS`
as search-v11/probe-v17; no new verbs or index changes.
All 122 search tests, 8 help tests, and expanded pinned-Lean CLI smoke pass.
Original dependency-copy replay now reports no literal source matches for the
absent term; a real theorem query matches its declaration and lone find retains
the comment matches. Installed prior API-usage routing independently passes.


## Dotted module outlines reach source resolution (i49)

Telemetry 149464/q294813 requested a dotted module outline but received lexical
results and file-body excerpts. A generic Demo.Facts replay reproduces the mismatch
with the equivalent Demo/Facts.lean outline. The source resolver already supports
dotted modules; the outline parser rejected their apparent filename extension first.

Inferred outline/declarations targets now use that existing path conversion and
resolver. Only a resolved file becomes an outline; a missing file leaves declaration
lookup available. Explicit Lean paths retain their handling. The regression fails
before the change and covers dotted/module-path equivalents and missing-file fallback.
Help is search-v12/probe-v17; no new verbs or index changes.
All 123 search tests, 8 help tests, and expanded pinned-Lean CLI smoke pass.
Generic dotted and slash-path replay return identical outlines. The original query
against a copied Sobolev module returns its 24 declarations and a source handoff.


## Regex-result source probes load the complete declaration (i50)

Telemetry 149481/q294837 requested source for a named regex result and received
only matched lines, labeled as an incomplete excerpt. A generic theorem replay
reproduced the failure; probing the same declaration by name loaded the full proof.
The current-file refresh rejected its source-group metadata as a declaration-kind
mismatch even though the exact declaration name matched.

Named source-group hits now use the same exact-name current-file refresh as generic
compiled hits. The refreshed kind/signature/body come from the authored declaration.
Unowned line matches have no matching declaration name and remain excerpts; no
proof or source completeness is inferred. No verbs, help contract, or index changed.
The regression fails before the fix; all 123 search tests pass.
Expanded pinned-Lean CLI smoke passes with a regex-to-qREF-source full-proof
regression. Generic replay confirms parity with direct-name source; an unowned
comment control remains an incomplete excerpt. The prior installed dotted-module
outline fix was independently verified.


## Regex case-pair recovery keeps complete words (i51)

Telemetry 149528/q294889 reports fallback literals ompact and ellich for a query
containing `[Cc]ompact` and `[Rr]ellich`. Isolated replay confirms the same malformed
recovery terms. This weakens the existing declaration recovery after zero regex hits.

Recovery extraction now normalizes same-letter ASCII case-pair classes to one
lowercase letter before extracting words. The regex matcher is unchanged; general
classes and ranges retain their previous recovery behavior. Results remain explicitly
closest declarations rather than regex matches. No verbs, help contract, or index changed.
The extended regression fails on the old extractor; all 123 search tests pass.
Expanded pinned-Lean CLI smoke passes. The original regex shape now reports full
compact/rellich recovery words, and a neighboring genuine case-pair regex still
returns its exact source match.


## Out-of-range reads give a concrete recovery (i52)

Telemetry 149550/q294895 requested lines 140-187 and received only “no source lines
in range”; the next read guessed 85-132. A generic short-file replay confirms the
same lack of a useful boundary or handoff.

An empty range now reports the current file's line count and suggests the existing
FILE:tail read. Empty files say they are empty without suggesting another empty
read. The earlier stale-workspace/main comparison retains precedence and still
requests sync. No verbs, help contract, or index changes.
All 123 search tests, including the existing stale-workspace regression, and
expanded pinned-Lean CLI smoke pass. Generic short-file read follows the suggested
tail successfully; empty-file replay has no retry. Installed prior regex recovery
was independently verified.


## File signature probes select declarations instead (i53)

Telemetry 149593 probes the signature of q294903#1, a file fallback with no
signature. A later source probe reads the whole module. Isolated comment-match
replay reproduces the current misleading “Signature is not indexed” message and
whole-file source handoff.

A single file hit now explicitly has no declaration signature and directs the
agent to the existing file outline, where named declarations can be selected.
Unsigned declaration hits retain their source recovery; signed hits retain their
signature. No verbs, help contract, or index changes. The extended renderer
regression includes a quoted path; all 123 search tests pass. Generic replay
follows the outline to the actual declaration. The CLI regression exercises the
comment-only file hit and its outline handoff in an isolated fixture.


## Signature probes expose the statement before context (i54)

Telemetry 149610 requests isCompactOperator_of_tendsto's signature; the preview
ends among typeclass binders, before either explicit hypothesis or the conclusion.
The next request reads a broad source range. Copying the dependency source into
an isolated replay reproduces this on the current build.

Signature probes now use the existing balanced-binder preview before applying the
same 240-character budget. Explicit premises and conclusion come first; elided
implicit/typeclass context is counted. Whenever the preview differs from the full
signature, an explicit `show qREF --all` handoff exposes the stored context. Short
complete signatures gain no extra line. The full stored signature is unchanged.
No new verbs or index changes. All 123 search tests pass, including shortened
context, long explicit inputs, and unchanged short signatures. The CLI regression
follows the full-signature handoff and checks every authored implicit input.
The original compact-operator replay now exposes both hypotheses and the conclusion.
Installed i53 file-outline behavior was independently verified.


## Attributed alias source preserves the replacement route (i55)

Telemetry 149617 cannot recover IsCompactOperator.finiteDimensional's source;
149618 reads the file instead. The declaration is an inline `@[deprecated] alias`.
The alias recognizer accepted only a bare alias at line start. A focused regression
fails on this exact attribute shape before the fix.

Alias recovery now accepts the same leading attribute syntax as the declaration
recognizer. The source snapshot includes the attribute, alias command and origin;
its existing origin handoff exposes the replacement theorem's premises. Exact
namespace matching and comment masking remain enforced. No new verbs, index or
help changes. All 123 search tests and expanded pinned-Lean CLI smoke pass.
Both the generic CLI fixture and copied original workflow model a compiled alias
hit in isolated stored results, then follow source recovery to the origin. They
do not claim source-only indexing generates aliases or that Mathlib was recompiled.


## Preserve complete signatures when they fit (i56)

Following telemetry 149629-149641 through the convex integral and average theorems
exposed an i54 regression: compaction hid IsProbabilityMeasure even though the
complete signature fit the existing 240-character budget. The average theorem's
IsFiniteMeasure and NeZero assumptions were similarly unnecessary omissions.

Signature probes now retain the complete signature whenever it fits. Only longer
signatures use context compaction and the full-context handoff. The same copied
workflow displays all three measure assumptions immediately; the neighboring long
compact-operator theorem still exposes explicit hypotheses and conclusion.
All 123 search tests pass. CLI coverage checks both full short inputs and a long
implicit-input signature whose handoff retrieves every stored input. No verbs,
index or help changes. The audit advanced through telemetry 149641; source probes
retain ambient assumptions and comment searches remain labeled source matches.


## Grouped data fields are part of field probes (i57)

Telemetry 149667 omits ContDiffBump's rIn/rOut data fields and shows only their
proof obligations. Source probe 149669 reveals `(rIn rOut : ℝ)`. A generic grouped
Nat-field fixture reproduces the omission on the current build.

The field parser now recognizes parenthesized grouped names and creates a field
entry for each name with the shared type and source line. The group participates
in field boundaries, so preceding fields do not absorb its source. Nested type
parentheses remain intact. Index version advances to 15 so persisted source
indexes regenerate the missing entries. No new verbs or help changes.
All 124 search tests pass, including grouped types, dependent fields and line
coordinates. Copied original source now yields both radii before their obligations.
The CLI regression checks generic grouped data and its dependent proof field.
Installed i56 short-signature and full long-context recovery passed independently.


## Unavailable source has a contract-recovery handoff (i58)

Telemetry 149700-149702 repeatedly requests source for generated additive support
declarations. Their authors used unnamed to_additive generation, so recovering a
separate authored body or inferring the generator name would be unreliable. The
existing no-source response correctly withholds a completeness claim but gives no
next action.

An unavailable-source response now suggests existing project-context #inspect for
the exact requested declaration, explicitly requiring an importing project file.
It still makes no source or mathematical completeness claim. Indexed excerpts
retain their existing treatment. No new verbs, index or help changes.
All 124 search tests pass. Copied original source with a modeled compiled result
confirms the exact-name handoff without inventing a source snapshot. CLI coverage
uses a real generated constructor and follows inspection to its datum obligation.
Installed grouped-field behavior was independently verified.


## Coverage uses consistent numeric spellings (i59)

Telemetry 149736 finds inv_le_inv₀ but warns that inv_le_inv0 is missing. Generic
isolated replay reproduces the false weak-coverage warning: query concepts include
a numeric alias that the coverage checker compares against unnormalized hit text.

Coverage now applies the existing ASCII numeric spelling normalization to both
hit text and requested terms. Exact declaration resolution, wildcard matching,
and displayed names are unchanged. Different digits still count as missing.
All 124 search tests pass, including both alias directions and a different-digit
control. Replay removes the spurious warning while retaining the source name and
signature. The CLI regression covers a qualified subscript-bearing wildcard.
No new verbs, index or help changes. Audit advanced through telemetry 149741.


## Broad discovery skips private macro helpers (i60)

Telemetry 149793 returns a private compiler macro helper for BumpFunction*, with a
long unusable source handoff. Copying the actual source and ilean artifact into an
isolated replay reproduces the helper ranked first both cold and warm. The name is
in compiled decls, rather than the generated-alias reference path.

Discovery ranking now excludes private names whose leaf is an auxiliary macroRules
helper. Exact full-name requests remain available; ordinary private declarations
are retained. The compiled index itself is unchanged. No new verbs or index changes.
All 125 search tests pass, including broad discovery, ordinary private declarations
and explicit helper requests. Replay of the original artifact now shows module
context first and still resolves the exact helper name. Full release gates remain
with the release owner.


## Escaped probe names cannot select another theorem (i61)

Telemetry 149819 passes a literal backslash-u0027 suffix and receives the unprimed
MemLp.mono declaration. Generic replay with differently typed mono and mono-prime
confirms the incorrect selection. Declaration probes now reject backslash escapes
before lookup and require literal name characters. They do not decode or rewrite
an ambiguous selector. Contextual Lean terms and forced type forms remain accepted.

The 125 existing search tests and new focused parser regression pass. Generic
replay rejects the escaped selector and retrieves the distinct literal primed
name. CLI regression checks that malformed input returns an error without a source
snapshot. No new verbs or index changes. This correction concerns declaration
probe selectors, not source regex syntax. Audit advanced through telemetry149819.


## Qualified source paths cannot collapse to a basename (i62)

Auditing missing dependency path recovery in telemetry149897 exposed a stronger
fault in a generic fixture: requesting Mathlib/Analysis/Fourier/L2Space.lean returns
an unrelated project-root L2Space.lean. The resolver appended a bare filename to
qualified path variants, enabling silent substitution.

Qualified paths no longer gain that bare-filename variant. Bare-name lookup,
explicit repeated-root shorthand, multi-component suffix recovery and valid
dependency paths retain coverage. An existing test that endorsed Wrong/Prefix/Nested
resolving solely by basename was updated to require an error. Other 125 search
tests passed, and the adjusted source-query regression passes. Expanded pinned-Lean
CLI smoke passes. Isolated replay rejects the missing qualified dependency while
still reading the project basename explicitly and the actual nearby dependency.
No verbs, help or index changes. Nearby-source suggestions remain suggestions.


## Prefer matching names in case-pair wildcard discovery (i63)

Telemetry 149984 uses ContinuousLinearMap.*[Tt]emperateGrowth. Independent
cold and warm replay against clean main ranks Function.HasTemperateGrowth.mul
first and the matching bilinear theorem fifth. Redundant case pairs prevent
ordinary name-glob recognition, leaving generic relevance in control.

Ranking now recognizes same-letter ASCII case pairs in otherwise ordinary globs
and stably promotes matching declaration names. Retrieval and fallback candidates
are preserved; arbitrary character classes are not reinterpreted as name globs.
No public verbs, query grammar, help digest or source-index changes.

The focused regression and all 127 search tests pass. Separate fresh indexes for
baseline and fixed builds reproduce the fifth-to-first improvement both cold and
warm. Existing output selection yields three displayed results instead of eight.
Neighboring plain globs, alternations and conceptual queries were also replayed;
source probing continues to expose both temperate-growth premises. Fixtures copy
dependency source into isolated repositories; no formalization work is run.


## Quoted private macro helpers obey discovery filtering (i64)

Telemetry 150025 exposes a private compiler macro helper whose leaf uses Lean
identifier quotes. The i60 filter recognized only an unquoted `_aux_` prefix.
Replay with copied SobolevInequality source and its real ilean artifact confirms
that the quoted helper can rank first in discovery. Remove one balanced pair of
identifier quotes solely for helper classification. Keep the stored name and
fully specified name retrieval unchanged; ordinary private declarations remain.

The extended focused regression and all 127 search tests pass. CLI-backend replay
excludes the helper from broad discovery and retains it first when its full name
is supplied. The full-name query already renders ranked results; an initial replay
assertion incorrectly required exact-declaration classification and was corrected
to check retained retrieval. No new verbs, help or source-index changes. Other
hygienic generated declarations seen in this fixture remain a separate audit.


## Exclude compiler hygiene implementation names from discovery (i65)

Replaying the telemetry 150025 discovery query with real copied source and ilean
reveals several `definition._@...._hygCtx._hyg.N` names ahead of usable declarations.
These have no indexed signature, and their source probes report unavailable.
Names carrying both compiler hygiene markers now follow the existing helper
filter: excluded from broad discovery, retained when fully specified. Public
generated names and ordinary `_hyg` names remain eligible. No index/help changes.

All 128 search tests pass. Real artifact replay removes hygiene names from the
broad query and returns the fully specified helper as its single result. The
replay assertion initially expected a numbered row; single-result rendering has
no #1 label, so validation checks the actual single-result output instead.
Remaining file matches are not claimed to answer the missing postcomposition API.


## Explain distributed query-term coverage (i66)

Telemetry 150081 searches for an elliptic estimate and receives separate elliptic
and estimate-related results. A generic two-file fixture reproduces this cold and
warm. Aggregate coverage intentionally remains complete, but previously supplied
no qualification that the terms were distributed across individual results.

Discovery now adds one sentence when returned results collectively cover all
query terms but no individual result does. This is textual matching, not a claim
about mathematical applicability or nonexistence. Ranking, retrieval and existing
weak-coverage semantics are unchanged. Exact/name/type requests and alternatives
are excluded from this qualification. No public verbs, help or index changes.

All 129 search tests pass. Focused cases cover split results, a complete individual
result, documentation coverage, missing terms and single-term queries. Isolated
replay verifies the note cold and warm and its absence for exact/alternative
controls. Formalization files and daemons remain untouched.


## Preserve owner/member name matches in coverage ranking (i67)

Telemetry 150167 searches HasTemperateGrowth mul and then resorts to the fully
qualified declaration. Isolated cold/warm replay reproduces unrelated top results.
Temporary candidate tracing confirms the intended theorem was retrieved with all
five expanded tokens covered; the loss occurs in ranking, not indexing.

At equal textual coverage, prefer a declaration whose qualified name matches the
original query words joined by dots. Use original words rather than expanded
identifier parts/aliases. Better textual coverage retains precedence; retrieval,
result count and public grammar are unchanged. No help/index changes.

All 130 search tests pass, including a regression with an excerpt and a longer
name containing the same words. Real source replay returns the intended theorem
first cold and warm; neighboring smul and mul_right lookups also return their
matching declarations. Earlier name-token-only tuning promoted an unrelated
longer name and was discarded. No diagnostic tracing remains in the product.


## Recover nearby compound names after an empty prefix lookup (i68)

Telemetry 150219 guesses Function.not_mem_support. Real source/ilean replay shows
Function.notMem_support exists, but full-prefix FTS rejects it before edit-distance
ranking. Empty near-name retrieval now retries the first underscore-delimited
component when at least three characters long. This uses the same scope and row
limits; successful initial retrieval and exact resolution remain unchanged.

All 130 search tests pass. Extended retrieval regression covers the shorter
prefix, inactive-workspace exclusion, short-prefix refusal and unchanged successful
lookup. Real artifact replay suggests the camel-case declaration first, explicitly
not exact, and retains direct lookup. No new verbs, help or index changes. This is
bounded recovery, not exhaustive fuzzy search or automatic selector rewriting.


### i69: recover an end-anchored declaration-pattern miss

Telemetry 150200–150226 contains empty declaration-pattern searches. A current isolated copy of Mathlib distribution sources reproduces `tsupport.*lineDeriv` returning only `no name match`, while `tsupport.*lineDeriv*` retrieves both support-containment declarations. The exact-ending behavior is correct, but the empty result leaves a recoverable spelling boundary unexplained.

Search now offers the trailing-star retry only after a name-pattern miss and only when an already retrieved declaration matches that extension. Single patterns already ending in `*`, alternatives, files, private/compiler helpers, and unsupported extensions produce no new hint. Matching semantics, retrieval, successful output, and public verbs are unchanged. The recovery matcher compiles once per eligible query.

Validation: 131 search tests pass, including evidence/empty/alternative/private/file controls. Fresh isolated replay (`/tmp/mm-i69-final.log`) preserves warming uncertainty, returns the retry on the original miss, retrieves the two declarations with the suggested query, and follows the selected declaration to its full source assumptions. A successful exact-ending pattern and unrelated `smulLeftCLM.*lineDeriv` miss remain unchanged. Debug replay timings after compiling once were comparable to baseline (213 ms versus 222 ms for the warmed original query); these are observations, not a benchmark claim. No formalization workspace or daemon was used.
