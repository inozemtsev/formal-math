# Sources and licenses

## Mathematical sources

The agent found **Jizhou Guo**'s manuscript *Shifted primes with a prescribed
parity of the number of prime factors* on GitHub during the final stage of
Lean formalization and used its exposition as a guide. The final
development follows the specialization of its
affine-prime-form argument to $N(u)=u+2$, including the choice of twenty
ordinary prime slots, the arithmetic side conditions, and the order of
analytic parameter choices. Guo's paper and this project build on the
OpenAI papers *Prime Predecessors with an Even Number of Prime Factors*
and *Weighted dilation graphs, smooth shifted primes and totient fibers*.

The initial work already pursued the same fixed-shift strategy before the
recorded consultation of Guo's paper. The
[source history and comparison](ACKNOWLEDGEMENTS.md) distinguish that
earlier work, the later influence, and the scope of the theorem proved here.
These are credits for mathematical sources, separate from the code and
license notices below.

## Incorporated Lean sources

Mathlib is the sole direct Lake dependency. Its exact revision and its
transitive dependencies are recorded in `lake-manifest.json`.
The additional supporting mathematics is included locally as Lean source.

| Source | Pinned revision | Incorporated material and notice |
| --- | --- | --- |
| [OpenAI math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | Adapted `OAI` analysis and number-theory modules, including local extensions. [Apache 2.0](licenses/OpenAIMath.txt). |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/c39a751132c88b6e8080b74c74023fd95b3d8be0) | `c39a751132c88b6e8080b74c74023fd95b3d8be0` | Analytic prime-number-theorem supporting sources. [Apache 2.0](licenses/PrimeNumberTheoremAnd.txt). |
| [Rellich–Kondrachov](https://github.com/abenenson/rellich-kondrachov/tree/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23) | `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` | Sobolev and compactness lemmas; Adam Benenson's source notices are retained. [Apache 2.0](licenses/RellichKondrachov.txt). |
| [Chen theorem formalization](https://github.com/lixiang90/chen_theorem/tree/11dcca8fc3ab340358503278c46d72aef072a6e7) | `11dcca8fc3ab340358503278c46d72aef072a6e7` | Adapted character-sum, zero-free-region, and sieve supporting sources under the `Chen` namespaces. See the qualification below. |

The local adaptation changes imports to `Green64.Library`, groups related
source units, updates compatibility imports for Lean 4.35.0-rc2, gives the
final proof a named public interface, and removes development-only
printing commands. Existing source attribution and copyright notices
are retained. The local extensions and the Green 64 argument are part
of this proof project; the upstream links do not claim that those
repositories already contain the complete Green 64 proof.

The Chen source revision has Apache notices for incorporated PNT and
linear-sieve material, reproduced in
[ChenPNT-NOTICE.txt](licenses/ChenPNT-NOTICE.txt) and
[ChenLinearSieve-NOTICE.txt](licenses/ChenLinearSieve-NOTICE.txt).
Its PNT notice identifies the separate upstream revision
`c6c73610b406689c4b58325cbe1342ecca25d755`; its linear-sieve notice
credits Arend Mellendijk and Mathlib 4.32.2.
On 2026-11-12 the current upstream `main` still resolved to this exact
revision. Inspection of the complete tree, both READMEs and source notices
found no repository-wide license for
its remaining sources. Reviewing all 71 commits reachable from that revision,
including historical READMEs and source notices, did not reveal a broader
license grant. This project therefore does not assign
an Apache license to that material. On 12 November 2026, a licence
clarification request was sent to the repository maintainer by email, asking
for the applicable terms or permission to distribute adaptations under
Apache-2.0 with attribution and notices retained. A reply and permission are
pending; the request does not establish a licence grant or endorsement.
The collection's root license
covers its own work and does not override third-party notices or supply
a missing third-party license.

Upstream repository links in this file document code provenance and
licenses. The required mathematical inputs are proved in the included Lean
development; they are not added as axioms.
