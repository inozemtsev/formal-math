#!/usr/bin/env bash
set -euo pipefail

# Local check using the kernels bundled with the pinned Lean toolchain.
# Adapted from PalomarRegistry/PalomarTemplate's verification script.
cd "$(dirname "$0")/.."
for required in lake lean bwrap python3; do
  command -v "$required" >/dev/null || { echo "$required is required" >&2; exit 1; }
done
prefix=$(lean --print-prefix)
for binary in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$binary" || { echo "Missing $binary in $prefix" >&2; exit 1; }
done
config=$(mktemp "${TMPDIR:-/tmp}/green64-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels is not a Palomar author configuration field')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(Path(prefix) / 'bin/nanoda_bin')],
    'con-ron': [str(Path(prefix) / 'bin/con-ron'), '--jobs=1'],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
lake comparator --config "$config"
