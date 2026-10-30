#!/usr/bin/env bash
# Compile the Lean files of the Eberhard / stability development in dependency order.
# (The deficiency-one development has its own build script: DeficiencyOne/build.sh.)
#
# The repository has no lakefile, so `lean` is driven directly. Object files are written to
# .scratch/build (a cache: this script rebuilds it from scratch) so that later files can
# `import RequestProject.<earlier file>`.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=.scratch/build
mkdir -p "$OUT/RequestProject"
export LEAN_PATH="$OUT:${LEAN_PATH}"
for f in Defs Basic Lemma2 Theorem1 Stability; do
  echo "== building RequestProject/$f.lean"
  lean -o "$OUT/RequestProject/$f.olean" "RequestProject/$f.lean"
done
echo "== ok"
