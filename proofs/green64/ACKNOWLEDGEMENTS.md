# Mathematical sources and provenance

Proof development and formalization: **gpt-6 astra**.

During the final formalization stage, the agent found **Jizhou Guo**'s
manuscript *Shifted primes with a prescribed parity of the number of prime
factors* on GitHub and used its exposition to guide the formalization.
Guo did not participate in the project or provide personal assistance.
This attribution credits the manuscript, not a collaboration or endorsement.

The initial project records of 7 October 2026 already proposed the fixed-shift
specialization of the OpenAI work cited below. The first recorded consultation
of Guo's manuscript is dated 4 November 2026. These are project milestones,
not claims of mathematical priority. The approaches share the same OpenAI
sources and have substantial overlap. The later manuscript helped steer the
formalization's final parameter choices and treatment of arithmetic conditions.

The submitted claims concern only odd prime-factor parity for the fixed shift
of two, as stated in Challenge. They do not establish every broader shift,
parity, squarefreeness or quantitative assertion in the cited sources.
Mathematical novelty and priority have not been established by a comprehensive
literature search and are not claimed. The source relationships and limitations
are also recorded in [formalization.yaml](formalization.yaml).

## Verification status of the OpenAI sources

The mathematical strategy and supporting arguments build on the two OpenAI
manuscripts cited below. Their
[accompanying README](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/README.md)
describes results at different stages of verification and warns that some
unformalized results may contain errors. No independent human verification
of these source manuscripts is claimed here.

The supporting inputs needed for the two Green64 statements are proved in
the included Lean development. The completed axiom audit reports only
`propext`, `Quot.sound`, and `Classical.choice`. The scope and limitations of
the machine checks are recorded in [VERIFICATION.md](VERIFICATION.md).
Those checks do not establish every claim of the source manuscripts or
constitute independent human review of their mathematics.

## Pinned mathematical sources

1. Jizhou Guo, *Shifted primes with a prescribed parity of the number of
   prime factors*, October 2026,
   [pinned TeX source](https://github.com/aster2024/openai-math-followups/blob/563cece082b628dfe3ba0290c9e4e30b92ffeca6/shifted-prime-parity/source/main.tex).
   Revision `563cece082b628dfe3ba0290c9e4e30b92ffeca6`;
   source Git blob `427e12762baaecac54e71a12ad765a7db9a22ddc`.
   The retained source was checked against that blob and SHA-256
   `05bcc2170bf407bbad9319d1f63754583e10c8835502b248cbfdceafc3f9c985`.
   The original URL returned 404 when rechecked on 12 November 2026;
   the comparison uses that identified local copy.
2. OpenAI, *Prime Predecessors with an Even Number of Prime Factors*,
   manuscript dated 17 September 2026,
   [pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/main.tex).
3. OpenAI, *Weighted dilation graphs, smooth shifted primes and totient
   fibers*, manuscript dated 24 September 2026,
   [pinned source directory](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026).

The OpenAI sources are pinned to
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Incorporated Lean code and its
license notices are documented in [THIRD_PARTY.md](THIRD_PARTY.md).
