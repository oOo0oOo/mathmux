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
