# Green's Problem 64

There are infinitely many primes $p$ such that $\Omega(p-2)$ is odd, where
$\Omega(n)$ counts prime factors with multiplicity. The development also
proves that such a prime exists above every natural bound, with $p-2>0$.

This is the fixed-shift question in Ben Green's
[*100 Open Problems*, Problem 64](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.64).
It concerns the Liouville parity of a fixed additive shift of primes, a question
in analytic number theory and sieve theory. It makes an infinitude claim;
no numerical threshold, uniform range of shifts, or squarefreeness assertion
is part of the two submitted theorems.

## Read the proof

- [Full proof — green64.pdf](paper/green64.pdf): the 83-page article, with detailed arguments and source correspondence.
- [Proof idea — proof-idea.md](docs/proof-idea.md): a short account of the weight, correlation estimate and sieve argument.
- [Proof in Markdown](docs/proof.md): the full exposition and its linked chapters.
- [Lean source guide](docs/lean-guide.md): the correspondence with the formal development.

The [article sources and build instructions](paper/README.md) reproduce the
PDF. The exposition follows the included Lean development; its short outline
links to the detailed estimates.

## Development timeline

The [development timeline](TIMELINE.md) records the initial plan, intermediate
results, revisions, article preparation and verification milestones. It makes
no claim of mathematical priority.

## Verification

The formal proof has passed the full [Palomar verification workflow in CI](https://github.com/inozemtsev/formal-math/actions/workflows/palomar-preflight.yml),
including a fresh source build, protected statement comparison and kernel
checks. The complete protected verifier has also passed locally. See
[VERIFICATION.md](VERIFICATION.md) for the reports, timings and scope.
Mechanical verification does not constitute registry registration or human
peer review.

## Exact statements

```lean
import Green64

open scoped ArithmeticFunction.Omega

example : {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite :=
  Green64.green_64

example (M : ℕ) :
    ∃ p : ℕ, p.Prime ∧ Odd (Ω (p - 2)) ∧ 0 < p - 2 ∧ M < p :=
  Green64.primes_unbounded M
```

Here subtraction is natural-number subtraction, and `Ω` is Mathlib's
`ArithmeticFunction.cardFactors`. It counts multiplicities: for example,
$p=11$ does not qualify because $\Omega(9)=2$. Mathlib sets
$\Omega(0)=\Omega(1)=0$, so $p=2$ and $p=3$ are excluded. There are no additional
hypotheses. The witness statement makes unboundedness and positivity explicit.

[Challenge.lean](Challenge.lean) states both claims using only Mathlib imports.
Its two deliberate proof holes are the inputs to statement comparison.
[Solution.lean](Solution.lean) proves the same declarations through
[Green64/Main.lean](Green64/Main.lean), independently of Challenge.
[comparator.json](comparator.json) selects those two declarations and permits
only `propext`, `Quot.sound`, and `Classical.choice`.

## Sources, authorship and scope

Green's source poses the question and is not cited as containing this proof.
The mathematical sources and the distinction from their broader statements
are recorded in [formalization.yaml](formalization.yaml) and
[ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md). The latter includes the source
consulted by the agent on GitHub during the final formalization stage.
No personal assistance by its author is claimed. Mathematical priority and
novelty have not been established by a comprehensive literature search and
are not claimed.

The strategy and supporting arguments build on the cited OpenAI manuscripts.
OpenAI describes results at different stages of verification and warns that
some unformalized results may contain errors. Independent human verification
of these manuscripts is not claimed here; see the
[source-status note](ACKNOWLEDGEMENTS.md#verification-status-of-the-openai-sources).
The supporting inputs needed for the two submitted Green64 statements are
proved in the included Lean development.

Proof development and formalization: **gpt-6 astra**.
No independent human mathematical review or Palomar endorsement is claimed.

The statement agrees with `Green64.green_64` in the
[formal-conjectures collection](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjectures/GreensOpenProblems/64.lean).
That repository is not a dependency of this project.

The project's own work is Apache-2.0 licensed. Incorporated supporting code,
its notices and the unresolved permission question for part of
`lixiang90/chen_theorem` are documented in [THIRD_PARTY.md](THIRD_PARTY.md).
A licence clarification request was sent to that repository's maintainer
on 12 November 2026; a reply and permission are pending. Contact does not
establish permission or endorsement.

## Reproduce the formal proof

The compiler is **Lean 4.35.0-rc2**. Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55` is the only direct Lake dependency;
its dependencies are pinned in `lake-manifest.json`. All additional supporting
mathematics is included as Lean source. This project does not import the other
proof in the collection.

With [elan](https://github.com/leanprover/elan) installed, run here:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 python3 scripts/verify.py
LEAN_NUM_THREADS=1 bash scripts/verify-comparator.sh
```

The initial source build includes a substantial supporting analytic library.
Python 3 is needed for the audit script, not for `lake build`. The Comparator
script requires an environment that supports bubblewrap namespaces.

[VERIFICATION.md](VERIFICATION.md) records the successful protected CI and
local verification, alongside the earlier source, statement and kernel checks.
[SOURCE_EQUIVALENCE.json](SOURCE_EQUIVALENCE.json) records that the submitted
Lean and build inputs are byte-identical to those used in the local checks;
only the descriptive metadata in that audit's hash list has changed.
[PALOMAR.md](PALOMAR.md) records the submission paths and pinned workflow.
