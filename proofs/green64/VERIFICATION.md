# Verification record

## Current submission configuration

[Version 1 is registered in Palomar](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-13-000010&version=1).
Its [complete CI preflight](https://github.com/inozemtsev/formal-math/actions/runs/43390233171)
and [Palomar verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43406667853)
passed, followed by automated editorial review.

The configuration for version 2 selects only `Green64.green_64`, removes the
supporting unbounded-witness statement from Challenge and updates the abstract.
The proof, dependencies, written article and PDF are unchanged. The
[full workflow](https://github.com/inozemtsev/formal-math/actions/workflows/palomar-preflight.yml)
checks the revised configuration on its source revision before the next submission.
Historical receipts below describe their original inputs, including the earlier
two-statement Challenge; they are not a passing report for the new configuration.

## Complete protected verification of the first version

The formal proof has passed the full [Palomar verification workflow in CI](https://github.com/inozemtsev/formal-math/actions/workflows/palomar-preflight.yml).
The [completed run](https://github.com/inozemtsev/formal-math/actions/runs/43325891223)
finished on 13 November 2026 at 03:12 Europe/Madrid after about 3 h 7 min.
Its [mechanical report](verification/github-mechanical-report.json) records
`status: pass`, with no errors or warnings. The checks include a fresh source
build, an independently compiled and protected Challenge, statement comparison,
Lean and NanoDa replay, and con-ron acceptance of 142,651 declarations.

The same protected verifier also passed locally at 04:39 Europe/Madrid,
in 16,241.26 seconds (about 4 h 31 min), within the 19,800-second shared
execution budget. The [local summary](verification/local-protected-summary.json)
records its scope and the checksum of the original report. Candidate build
state was fresh; the pinned Mathlib dependency cache is permitted by the
profile. These are complete protected checks, separate from the earlier
incremental builds and unsandboxed diagnostics below.

The article and documentation were added after those runs, with the same formal
inputs, before version 1 was registered. Historical reports retain their original
source identity; the subsequent version 2 selection is described above.
The [workflow page](https://github.com/inozemtsev/formal-math/actions/workflows/palomar-preflight.yml)
shows the CI result for each subsequent revision. Palomar intake uses a passing
report for the exact submitted revision. Mechanical success is not editorial
review, registration, endorsement or independent human peer review.

## Earlier source and kernel checks

The earlier receipts are preserved unchanged.
[SOURCE_EQUIVALENCE.json](SOURCE_EQUIVALENCE.json) records the comparison made
before version 1 was registered: its audited Lean, build, dependency and verifier
files were byte-identical, while descriptive metadata had changed. It is a
historical receipt, not a source comparison for the revised submission files.

The Lean 4.35.0-rc2 source build, exact-statement tests and axiom audit passed
on 12 November 2026. All 956 internal Green64 modules, the public entry point,
Challenge and Solution compiled successfully. Both exported theorems use only
`propext`, `Classical.choice` and `Quot.sound`. All nine dependency checkouts
match their pinned revisions and have unchanged tracked files.

[VALIDATION.json](VALIDATION.json) records the compiler commit, dependency
revisions, source hashes and audit results. The audit's repeated `lake build`
took 5.281 seconds using the completed build cache; this is not a cold-build
timing. The exact-statement and axiom checks took 4.575 and 12.390 seconds,
respectively. The final source-build pass completed 311 further modules during
the migration in 3,654.898 seconds; earlier passes had compiled the rest.

Comparator accepted the independent Challenge and Solution statements. NanoDa,
fresh Lean-kernel replay and con-ron all accepted the complete Solution export.
The Lean replay starts from an empty environment and checks the exported
theorem dependency closure; this is separate from replaying every declaration
in every imported module. The comparison with NanoDa and Lean took 902.343
seconds. Con-ron accepted 142,651 declarations with `--verified --jobs=1` in
829.271 seconds, within its 1,800-second cap.

The uncompressed Solution export contains 2,394,876,804 bytes and took 195.064
seconds to produce. The entire local export and kernel run took 1,932.856
seconds; its maximum reported child-process RSS was 9,963,524 KiB. These figures
exclude the source build and the registry's trusted setup, so they do not
measure the complete protected workflow. All audited source hashes remained
unchanged. [KERNEL_VALIDATION.json](KERNEL_VALIDATION.json) records success,
export and tool hashes, per-phase results and checker output. The run completed
at 21:07 UTC on 12 November 2026. It is a local diagnostic without the sandbox,
not a Palomar result.

The earlier Lean 4.34.1 source build, statement and axiom audits, and fresh
Lean-kernel replay passed at collection commit
`9f7abe25f1efdf1609a312f4e5eb4b474b23b296`. Its original verification
record and receipts remain in that commit; they do not certify this port.

The published default Palomar runner's host preflight was also evaluated on
the local machine on 12 November 2026. It rejected the host at the CPU check:
4 effective CPUs versus the required 16. The observed memory capacity was
about 15.4 GiB, and free workspace about 0.9 GiB, below that profile's 28 GiB
and 20 GiB minima. These are local environment limitations, not a verdict on
the proof. The profile and its time budget are described in
[PALOMAR.md](PALOMAR.md#registry-execution-profile).

The initial `palomar-standard-v1` preflight also rejected the available
workspace. After clearing reproducible build caches on 12 November 2026,
the official capacity check passes with more than 24 GiB free. The profile
permits the machine's four effective CPUs and approximately 15.4 GiB of
memory. Cgroup delegation passes as well. [HOST_PREFLIGHT.json](HOST_PREFLIGHT.json)
records these checks; they are not source or kernel checks.

The pinned bubblewrap 0.12.0 was built. Its namespace smoke test initially
failed under the host's AppArmor restriction, then passed after the official
path-specific profile was installed. Global namespace restrictions were not
disabled. The subsequent complete protected runs passed as recorded above;
the earlier unsandboxed diagnostic remains a separate check.

Local diagnostic controls from the pinned Palomar verifier passed on
12 November 2026. Lean, NanoDa and con-ron accepted the matching valid export
and rejected the deliberately ill-typed proof. Comparator rejected both a
mismatched theorem statement and an additional forbidden axiom. These small
controls used the verifier's exact test sources and ran without the sandbox;
they establish checker behaviour on those examples, not acceptance of Green64
or verification by Palomar.
