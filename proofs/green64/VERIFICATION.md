# Verification record

The local checks below apply to the formal inputs retained from preparation
commit `1ecdaed9f4c4fb9b792cbd6cb8f89b5624f8790f`. The receipts are preserved
unchanged. Their audited Lean, build, dependency and verifier files are
byte-identical in this submission; the only changed file in the original
source-hash manifest is the descriptive `formalization.yaml`.
[SOURCE_EQUIVALENCE.json](SOURCE_EQUIVALENCE.json) records that comparison and
both metadata hashes. No new local build or kernel run is claimed for the
metadata-only revision. Palomar's full workflow independently checks the exact
submitted commit and supplies its own report.

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
disabled. A complete protected workflow remains to be verified; the earlier
local diagnostic without the sandbox does not establish that result.

Local diagnostic controls from the pinned Palomar verifier passed on
12 November 2026. Lean, NanoDa and con-ron accepted the matching valid export
and rejected the deliberately ill-typed proof. Comparator rejected both a
mismatched theorem statement and an additional forbidden axiom. These small
controls used the verifier's exact test sources and ran without the sandbox;
they establish checker behaviour on those examples, not acceptance of Green64
or verification by Palomar.
