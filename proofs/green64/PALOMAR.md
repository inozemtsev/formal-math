# Palomar submission configuration

The selected project is `proofs/green64` in the proof collection. Palomar
supports a project below the repository root under
[policy section 6.1](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#61-a-lean-project-below-the-repository-root).
The selected directory supplies its toolchain, Lake configuration and metadata;
the repository root supplies `LICENSE`. The other proof remains an independent
project. Palomar's source-format checks inspect all repository Lean files.

The submission selects a commit of `main` using these repository-relative paths:

| Field | Value |
| --- | --- |
| Repository | `inozemtsev/gradient-supremum` |
| Selected project | `proofs/green64` |
| Comparator configuration | `proofs/green64/comparator.json` |
| Metadata | `proofs/green64/formalization.yaml` |
| Challenge module | `Challenge` |
| Solution module | `Solution` |
| Compared declarations | `Green64.primes_unbounded`, `Green64.green_64` |

The full mechanical workflow selects the exact commit through `github.sha`.
A workflow run is a preflight check, not registration or editorial approval.

## Required toolchain

The authoritative minimum is recorded in
[PalomarSubmission/toolchains.json](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json):

```json
{"schema_version":2,"minimum":"v4.35.0-rc2"}
```

This requirement is more specific than the short submission guide. This
project uses Lean `4.35.0-rc2` and canonical Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; that revision's
[lean-toolchain](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/lean-toolchain)
specifies the same compiler. All nine Git packages are pinned by full commit
SHA in the manifest. Mathlib remains the sole direct Lake dependency.

## Statement separation and checks

`Challenge.lean` imports only Mathlib and declares the two exact propositions.
Its two deliberate `sorry` terms are statement holes. `Solution.lean` imports
the complete proof through `Green64`, independently of the Challenge.
The compared names have no extra hypotheses or substituted definitions.
The only permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

After downloading the Mathlib cache, run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 python3 scripts/verify.py
LEAN_NUM_THREADS=1 bash scripts/verify-comparator.sh
```

The local comparison uses the pinned compiler's `lake comparator`, Lean
kernel, NanoDa and con-ron, with bubblewrap enabled. Its temporary kernel
configuration is kept outside the submitted `comparator.json`. Both external
kernels must accept for this local command to succeed. The registry's runner
has additional protected-build and provenance checks; it also distinguishes
specified con-ron support/capacity declines from proof rejection. A local
command is not a Palomar verification or editorial-review result.

Current results and source-hash receipts are in [VERIFICATION.md](VERIFICATION.md).
The prose description, source relationships, AI contribution, scope and review
status are recorded in [formalization.yaml](formalization.yaml). The full informal proof and PDF article are being revised separately and
are not part of this submitted version.

## Registry execution profile

At the verifier revision cited above, the default approved profile is
`palomar-namespace-16x32-v1`: a 16-CPU runner, with at least 28 GiB of
effective memory and 20 GiB of free workspace. The shared execution budget is
19,800 seconds (5 hours 30 minutes), within a 350-minute workflow job timeout.
The budget includes trusted setup and the subsequent verification phases.
These settings are published in the
[execution-profile catalogue](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/execution-profiles.json)
and the common
[verification profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/verification-profile.json).

An external caller of the reusable GitHub workflow must instead select
`execution_profile: palomar-standard-v1`, as specified in the
[workflow instructions](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md#L117).
That profile uses GitHub-hosted Ubuntu, requires at least 14 GiB of effective
memory and 20 GiB of free workspace, and has the same time budget. The
Namespace runner labels belong to Palomar. The profile is a workflow input,
not a field in the submitted Comparator configuration.

The current local machine lacks the free workspace required by either profile.
Its source-build
and kernel checks remain useful diagnostics, but cannot establish that the
complete protected workflow fits the registry's resource budget. In
particular, an incremental build time must not be reported as a fresh
submission's verification time.

## Full mechanical workflow

[palomar-preflight.yml](../../.github/workflows/palomar-preflight.yml) calls
the official reusable workflow in `mode: full`, with both its workflow and
pipeline revision pinned to `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
It selects `palomar-standard-v1` and the project paths above. A successful
local source build or standalone Comparator run does not replace this check.
The actual run and artifact, not this document, establish its outcome.

## Third-party licence request

The qualification in [THIRD_PARTY.md](THIRD_PARTY.md) remains unresolved.
A licence clarification request was sent to the repository maintainer by
email on 12 November 2026; a reply and permission are pending. The root
Apache-2.0 licence does not supply missing third-party permission.
