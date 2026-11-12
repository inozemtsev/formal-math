#!/usr/bin/env python3
"""Build from local sources, check the public statement and audit its axioms."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
THREADS = os.environ.get("LEAN_NUM_THREADS", "1")
ENV = dict(os.environ, LEAN_NUM_THREADS=THREADS)
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = ["Green64.primes_unbounded", "Green64.green_64"]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, name, timeout):
    destination = ROOT / ".lake" / "verification"
    destination.mkdir(parents=True, exist_ok=True)
    log = destination / (name + ".log")
    start = time.monotonic()
    with log.open("w") as stream:
        completed = subprocess.run([LAKE, *args], cwd=ROOT, env=ENV,
                                   stdout=stream, stderr=subprocess.STDOUT,
                                   timeout=timeout)
    output = log.read_text()
    return {"command": ["lake", *args], "exit_code": completed.returncode,
            "seconds": round(time.monotonic() - start, 3),
            "warnings": len(re.findall(r"(?m)^warning:", output)),
            "log": str(log.relative_to(ROOT)), "log_sha256": sha256(log)}, output


def main():
    checks = []
    receipt = {"passed": False, "checks": checks}
    try:
        compiler, output = run(["env", "lean", "--version"], "compiler", 60)
        checks.append(compiler)
        receipt["compiler_version"] = output.strip()
        expected = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
        if compiler["exit_code"] or not re.search(r"\bversion " + re.escape(expected) + r"(?:[, )]|$)", output):
            raise RuntimeError("The selected compiler does not match lean-toolchain")
        build, _ = run(["build"], "build", int(os.environ.get("GREEN64_BUILD_TIMEOUT", "21600")))
        checks.append(build)
        if build["exit_code"]:
            raise RuntimeError("The source build failed; see .lake/verification/build.log")
        audit, output = run(["env", "lean", "-j" + THREADS, "scripts/AxiomAudit.lean"],
                            "axioms", 1200)
        checks.append(audit)
        statement, _ = run(["env", "lean", "-j" + THREADS, "scripts/StatementTests.lean"],
                           "statement", 1200)
        checks.append(statement)
        axioms = {}
        for theorem in THEOREMS:
            found = re.search(re.escape("'" + theorem + "' depends on axioms:") +
                              r"\s*\[([^\]]*)\]", output)
            if not found:
                raise RuntimeError("Missing axiom report for " + theorem)
            axioms[theorem] = sorted(part.strip() for part in found[1].split(",") if part.strip())
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        dependencies = {}
        for package in manifest["packages"]:
            name = package["name"].removeprefix("«").removesuffix("»")
            directory = ROOT / manifest["packagesDir"] / name
            revision = subprocess.check_output(
                ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
            clean = subprocess.run(["git", "-C", str(directory), "diff", "--quiet", "HEAD", "--"],
                                   check=False).returncode == 0
            dependencies[name] = {"revision": revision, "expected_revision": package["rev"],
                                  "tracked_files_unchanged": clean}
        sources = [ROOT / name for name in ["Green64.lean", "Challenge.lean", "Solution.lean",
                   "lakefile.toml", "lake-manifest.json", "lean-toolchain", "comparator.json",
                   "formalization.yaml", "scripts/verify-comparator.sh"]] + [Path(__file__)]
        for folder in ["Green64", "scripts"]:
            sources.extend(sorted((ROOT / folder).rglob("*.lean")))
        receipt.update({"toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                        "threads": int(THREADS), "axioms": axioms,
                        "dependencies": dependencies,
                        "source_sha256": {str(p.relative_to(ROOT)): sha256(p) for p in sources}})
        receipt["passed"] = (all(check["exit_code"] == 0 for check in checks)
                             and all(set(value) <= AXIOMS for value in axioms.values())
                             and all(item["revision"] == item["expected_revision"]
                                     and item["tracked_files_unchanged"]
                                     for item in dependencies.values()))
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        receipt["error"] = str(error)
    (ROOT / "VALIDATION.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in {"source_sha256", "dependencies"}}, indent=2))
    return 0 if receipt["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
