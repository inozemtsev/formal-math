# Green64 exposition revision

This report records the initial 79-page exposition revision. The later
[PDF-only expert reviews and repairs](PDF_REVIEW.md) supersede the artifact
page count and conversion totals below.

Date: 12 November 2026. Formal source inspected at
`1ecdaed9f4c4fb9b792cbd6cb8f89b5624f8790f`, branch `palomar/green64`.
The article remains in English. This revision concerns the mathematical
exposition and article files; it is not a new formal-validation receipt.

## Response to the supplied reader comments

| Objection | Revision |
| --- | --- |
| Endpoint tests and probability spaces were unspecified. | (M0) defines the full joint product space, harmonic probability, arbitrary endpoint functions and independent permutation averages. (M0a) gives the exact phase and its dependence on the shared divisor, shift and orientation. |
| Arithmetic states, OLD labels, promotion and background births were undefined. | (T1)–(T5) define the residue spaces, ordered and multiset memory spaces, their masses, the quotient maps and the literal transition. OLD residues have counting measure; repeated atoms retain their multiplicity factorial. (T20) specifies background deletion and birth coefficients, including signs and factorials. |
| The transfer of (M1)–(M3) to (F7) was only asserted. | (M4a) defines the exact matching reference. (T6)–(T12) give the frozen form, the signed residual identity, the common density isometry, and separate density and collision errors. (T13)–(T17) disintegrate the SMALL fibres and Fourier-transform every translated OLD occurrence, retaining the full phase. (M11)–(M13) and (T18)–(T19) supply the rare promotion/store estimates and the full operator bounds. |
| The constants were given only through references to Lean. | (T21)–(T23) specify the SMALL masses, row constants, prefactor, contraction and loss parameters. The text distinguishes quantities depending on L from their fixed polynomial exponents. (M20a) specifies the path window and the endpoint constants. |
| The same-integer density and collisions were hidden by an independence argument. | (M16a) gives the residue average for each numerical prime. (T24)–(T25) prove its lifespan expansion and explain the transition correspondence. (M17)–(M18) retain the signed main term while applying CRT to the absolute error. The seed interval and padded matrix carrier are now distinct and explicit. |
| The prime-average and bilinear conclusions were not visibly connected to the local estimate. | (M23a)–(M23i) give the rank counts, coupled auxiliary law, exact endpoint functions, free-auxiliary collision error, and Mellin–circle identity. (U1)–(U5) state and derive the separate high-frequency prime estimate. (B19a)–(B19b) pay the growing Fourier norm before summing shifts and scales. |
| The short companion range and bounded-coefficient quantifiers were unclear. | The statement of (B3) fixes its parameters before the lower range exponents and allows every bounded companion coefficient. The first coefficient in (B18) remains the actual restricted discrepancy, and its residual is the actual ordinary-slot coefficient. The text explains the fixed positive range eta = b1/12 and the scale of the estimate for a singleton companion set. |

Every substantial added interface has a declaration-level source map in
the correspondence appendix. The proof distinguishes three carriers:
independent prime coordinates, residue-and-memory states, and integer
positions. In particular, (F7) is not presented as a norm bound obtained
by identifying the last two spaces. Their connection is the restored
history identity, CRT transfer, and positive matrix moment.

## Critical reading and repairs

A reader in a fresh context read the manuscript snapshot without Lean or
the earlier editing transcript. Its first report found no demonstrated
normalization error in (T6)–(T18), but identified five remaining interfaces:

1. The literal comparison-to-arc identity was missing. It is now (M23c)–(M23i),
   with the weighted shared restoration and the separate free-auxiliary error.
2. The zeroth Fourier moment was treated as a fixed bound. The actual bound
   is `C_0' L^{p_0}`. The requested correlation saving is now
   `D_1 = D_main + p_0`, exactly the extra precision used by the Lean proof.
3. A finite matrix could have imposed history-dependent boundary restrictions.
   The seed interval is now inside a carrier padded by the maximum displacement
   of a complete `2R`-step path. Every history from the seed interval fits;
   no signed history is discarded at the carrier boundary.
4. High-frequency prime cancellation was attributed only to a declaration.
   The text now states its exact clipped-interval, conductor and frequency
   ranges and gives the smoothed Mellin-contour deduction.
5. The reference resampling kernel was ambiguous. (M4a) now specifies the
   product-matching kernel and the phase substitution that it performs.

A subsequent source-assisted check of the comparison formulas found two
small corrections: the circle phase must be `e(-2kuv theta)`, and the
Fourier moment derivative orders are P and P+1. Both were corrected.
The checks found no further error in the displayed conjugations, the
factor `1/n`, or the independence of the final endpoint tests from the
auxiliary draws. This is an agent review, not an independent human referee report.

## Analytic input and provenance

The zero-free region (U2) was checked directly against
[Khale, Theorem 1.1, page 1](https://arxiv.org/pdf/2210.06457#page=1).
It is the same weaker input represented by the included
`SourceKhaleZeroFree`/`KhalePublished11` interfaces. The source correspondence
also records that the unconditional Lean theorem obtains it from the
stronger included seven-eighths nonvanishing theorem. The mathematical
deduction of (U1) needs only (U2); it does not require a reader to accept
that stronger conclusion solely on a kernel receipt. No argument from an
unverified external manuscript was added.

The Guo attribution remains explicit: the agent found the manuscript on
GitHub at the final stage; Guo did not participate or provide personal
assistance. No priority claim was added.

## Artifact checks

- Regenerated all sections with `python3 proofs/green64/paper/from_markdown.py`.
  Its exact math-payload comparison preserved 2,294 Markdown math nodes.
- Built the 79-page PDF using the three-pass `paper/build.sh` workflow.
  No TeX errors, undefined references, missing glyphs or overfull boxes remain.
- Checked all local Markdown link targets and all prose formula references.
  Removed the duplicate (F3) label by naming the block-sieve formulas
  (BS1)–(BS3), and updated their references.
- Verified that the named declarations in the new source tables occur in
  their linked Lean files.
- Visually inspected the pages containing the main transfer identities,
  bilinear Fourier budget, comparison pairing, high-frequency prime lemma,
  and source tables. A malformed prime-condition label found in this pass
  was corrected before the final rebuild.
- `git diff --check` passed. Lean files, toolchain, dependencies and validation
  records have no changes from this work. Concurrent coordination-file edits
  were left untouched. No branch switch, commit, push or external submission
  was performed.

The focused review leaves no identified unresolved blocker in the expanded
central transfer or the repaired interfaces to (B18)/(B3). This conclusion
concerns the displayed argument and its stated analytic inputs; it does not
claim a new audit of the complete formal development or a proof of all
standard analytic theorems reproduced from first principles.
