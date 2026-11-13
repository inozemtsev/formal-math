# Mathematical proofs

Mathematical proofs and their Lean formalizations. Each project contains its
own exposition, Lean sources, pinned compiler and Mathlib versions, and
verification commands. Mathlib is the only direct external Lean dependency
of each project.

| # | Result | Mathematical proof | Lean project |
| --- | --- | --- | --- |
| 1 | Supremum preservation under a gradient step | [Proof](proofs/gradient-supremum/docs/proof.md) | [Sources and build](proofs/gradient-supremum/) |
| 2 | Green's Problem 64: odd prime-factor parity at a shift of two | [Full proof (PDF)](proofs/green64/paper/green64.pdf) · [Proof idea](proofs/green64/docs/proof-idea.md) · [Markdown](proofs/green64/docs/proof.md) | [Sources and build](proofs/green64/) |

Green 64 includes a complete written proof and a Lean formalization. Its
[development timeline](proofs/green64/TIMELINE.md) records the main milestones
without claiming mathematical priority. The formal proof has passed the full
[Palomar verification workflow in CI](https://github.com/inozemtsev/formal-math/actions/workflows/palomar-preflight.yml).

## Building an individual proof

Enter the project's directory. For example:

```sh
cd proofs/gradient-supremum
lake exe cache get
lake --wfail build
python3 scripts/verify.py
```

The projects are independent and do not import one another. Their
`lean-toolchain` and `lake-manifest.json` files select their own compiler and
dependencies. See each README for its theorem statements and verification
commands. The Green 64 project is selected for Palomar through
`proofs/green64/comparator.json`.

## Attribution and licenses

Proof and formalization: **gpt-6 astra**. The collection's own work uses the
[Apache 2.0 license](LICENSE). Each project's `THIRD_PARTY.md` records
incorporated sources and their terms, including unresolved redistribution
qualifications.
