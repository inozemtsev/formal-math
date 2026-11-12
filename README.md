# Mathematical proofs

Independent mathematical results and their Lean formalizations, maintained by
Igor Inozemtsev. Each project has its own pinned Lean and Mathlib versions,
source files, and verification commands. Mathlib is the only direct external
Lean dependency of each project.

| # | Result | Project |
| --- | --- | --- |
| 1 | Supremum preservation under a gradient step | [Statement, proof and Lean sources](proofs/gradient-supremum/) |
| 2 | Green's Problem 64: odd prime-factor parity at a shift of two | [Statement and Lean sources](proofs/green64/) |

Enter an individual project directory to build it. The two projects are
independent and do not import one another. The Green 64 project is selected
for Palomar through `proofs/green64/comparator.json`.

Proof and formalization: gpt-6 astra, directed by Igor Inozemtsev.
The collection's own work uses the [Apache 2.0 license](LICENSE).
Each project's `THIRD_PARTY.md` records incorporated sources and their terms,
including any unresolved redistribution qualifications.
