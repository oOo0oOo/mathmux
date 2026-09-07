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
