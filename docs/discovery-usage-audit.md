# Discovery usage audit: probe-v6 through probe-v8

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
