#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
  xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
    -output-directory=build -jobname=green64 main.tex >"build/pass-${pass}.txt"
done
cp build/green64.pdf green64.pdf
