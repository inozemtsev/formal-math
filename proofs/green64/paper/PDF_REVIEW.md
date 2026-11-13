# PDF-only expert reviews

Three reviewers in fresh contexts read the complete 79-page manuscript
snapshot r0: the introduction, Sections 1–12, and Appendices A–B. They
received only the PDF and the review task. They did not receive the author’s
chat history, earlier findings, Markdown, TeX, Lean, or validation records.
The passes ran sequentially, without passing one reviewer’s verdict to the
next. Their roles were proof adversary, counterexample reviewer, and expert
first reader. All three reported reading the entire document.

The requested central chain was (M1)–(M3) → (F7) → (B18)/(B3), including
the measures, phase, arithmetic transfer, collisions, CRT, short companion
range, bounded-coefficient quantifiers, and order of parameter choices.
The scope also included the mass estimate, congruence estimates, finite
sieve, final subtraction, navigation, and unnecessary explanations.

None of the three initial readings found a demonstrated mathematical
error or a substantiated proof-critical gap. The counterexample reviewer
found one minor boundary-definition gap. The other findings concerned
redundancy and navigation. These are manuscript assessments, not a new
proof certificate or a formal-validation receipt. The reviewers accepted
the stated standard analytic inputs and did not verify their external
proofs or the Lean correspondence.

## Snapshots and rounds

| Revision | Pages | SHA-256 | Review |
| --- | --- | --- | --- |
| r0 | 79 | `9cc6feed21ccaf170790d8b3933a2cda067c43121ea5808f3229fd849f39dbbe` | Three independent, complete PDF readings. |
| r1 | 84 | `25310a5e8f4a12dfb7f0248e1d7bb8ff38328b83908946133cfe69b5465392dc` | Targeted PDF-only recheck closed the boundary, duplication, proxy and map-reference findings; found residual source-file references and two layout issues. |
| r2 | 83 | `8b712c4c32bd8d8252ba0cc0b9ada9a198d52d499a36e4ae657ccf77f34e3906` | Final targeted PDF-only recheck closed all remaining findings. |
| r3-editorial | 83 | `0d3e7d1ea42358009aa0b125f7bb405f959bc424cba9056a837ed6023ecb880f` | Source-provenance paragraphs clarified against the fixed OpenAI README; mathematical PDF text and pagination identical to r2. |

The immutable review copies and input-hash receipts were retained under
`/tmp/green64-pdf-review/r0`, `r1`, `r2`, and `r3-editorial`. The current article’s build
record is [PDF_BUILD.json](PDF_BUILD.json).

## Finding ledger

| ID | Original location and category | Repair | Status and closure evidence |
| --- | --- | --- | --- |
| PDF-01 | r0 main text, especially pp. 7, 10–15 and 63–68; excessive formalization commentary | Removed declaration-only sentences and source-file references from the mathematical body. Retained precise correspondence in the appendices and the source attribution in the front matter. Removed implementation-performance commentary from A.2. | Verified in r2, pp. 66–68. The r1 recheck closed the long-identifier and performance portions; the final recheck confirmed removal of the residual module references and checked their replacement by the actual dyadic partition and area/side bounds. |
| PDF-02 | r0 (C4) and the general rectangle sums, pp. 12, 59, 63; minor boundary-definition gap | Explicitly set `w_rho(0)=0`; use `R_W(m)R_W(n)` in both general rectangle sums and in the assignment constraints. The roughness indicator excludes 0 and 1. | Verified in r1, pp. 5, 61, 65. The editor also checked `sourceD20Rough` in `Weights/Part012.lean` (`2 ≤ n ∧ y < n.minFac`) and `sourceRoughBox` in `Sieve/WeightedBoxes.lean`. The zero-weight extension agrees with the vanishing cutoff in `localizedMass`. |
| PDF-03 | r0 §12.2 versus §11.4; duplicated rectangle normalization | Kept the proof in §11.4, recalled (S2) in §12.2, and linked to the normalization. Retired the unused duplicate labels (S3)/(S4); no references to them remain. | Verified in r1. The remainder estimate (R13), mass normalization and uniformity precede the application. |
| PDF-04 | r0 §3.3; excessive proxy normalization | State directly that `0 ≤ B_I ≤ 1` on the relevant cells and apply the bilinear estimate in either order. Retain the conservative `Q,2Q` bounds used in (C10). | Verified in r1, p. 13; the larger subsequent error budgets remain valid. |
| PDF-05 | r0 A.1; source-map links pointed to the mathematical chapters | Link to the actual correspondence headings, distinguishing the derivation from its source map. | Verified in r1 using actual PDF destinations: B.2, B.3, B.7, B.9. |
| PDF-06 | r1 p. 75; source-map heading stranded before its table | The converter reserves space before a source-map heading and its PDF anchor. | Verified in r2: B.2 and the first table rows are together on p. 75; visually confirmed by the final reviewer. |
| PDF-07 | r1 link from §12.2 to §11.4; destination before the heading’s page break | Reserve heading space before emitting the anchor, also for ordinary subsections. | Verified in r2: the final reviewer checked that the named destination and §11.4 heading are both at the top of p. 64. |

## Artifact checks

- Regenerated TeX from Markdown; the converter preserved all 2,280 math
  payloads of the revised source exactly.
- Built the 83-page PDF in three XeLaTeX passes. No compiler errors,
  undefined references, missing characters or overfull boxes were reported.
- All 12 main sections, both appendices and the bibliography begin on fresh
  pages. The contents occupy two pages. Changed pages, source tables and
  the two repaired destinations were visually inspected.
- Checked local Markdown targets, formula references and the new source
  table entries. No inline Lean-file links remain in the mathematical body.
- During the final build, all article input hashes were identical before
  and after compilation. The exported PDF, build output and current revision copy
  have the same SHA-256. This guards against an unnoticed overwrite of the
  reviewed changes; `PDF_BUILD.json` records the exact inputs.
- Lean files, toolchain, dependencies and formal-validation records were
  not edited. Concurrent coordination and provenance edits were preserved.
  No commit, push or external submission was made.

The final PDF-only recheck explicitly closed all remaining findings. It
also confirmed that the normalized text of Sections 4–8 is unchanged from
r1, including the central transfer argument. The review stopped after two
repair cycles and the final targeted check, with no unresolved accepted
finding or identified material reader blocker. The three initial readings
were independent; the later checks were targeted follow-ups by the expert
first reader, not fresh independent full-proof reviews.


## Subsequent editorial integration

The source-provenance paragraphs were clarified after the PDF review. The
[OpenAI collection README at the fixed revision](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/README.md)
was read directly. It describes differing verification stages and possible
issues in unformalized results; it does not establish that the source
manuscripts have never been reviewed. The article makes no claim of their
independent human verification and distinguishes their contribution to the
strategy from the supporting results proved in the included Lean development.

The author name and gpt-6 astra credit remain. No statement of the author's
direction, maintenance or personal support appears in the article. The Guo
attribution continues to describe the agent finding his manuscript on GitHub
at the final stage, without personal assistance or participation.

This integration changed only the source-provenance paragraphs in
`main.tex`. Every mathematical Markdown file and generated section matches
the r2 input hashes. The extracted PDF text, including page breaks and page
numbers, from Section 1 through the bibliography is identical to r2. This
was an editorial and build check, not a new independent mathematical review.
