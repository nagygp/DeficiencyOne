#!/usr/bin/env bash
# Compile the DeficiencyOne development in paper order.
#
# There is no lakefile in this repository: `lean` is driven directly and the object files are
# written to .scratch/build (a cache, rebuilt by this script) so that later files can
# `import DeficiencyOne.<earlier file>`.  Requires the Lean toolchain on PATH and LEAN_PATH
# pointing at Mathlib, both of which this VM provides.
#
# `DeficiencyOne/Defs.lean` reuses the `PGL2` infrastructure of the sibling Eberhard project
# (`RequestProject/Defs.lean`), and `Section2FixedPointBound.lean` uses Eberhard's theorem
# (`RequestProject/Theorem1.lean`), so those are built first as prerequisites.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=.scratch/build
mkdir -p "$OUT/RequestProject" "$OUT/DeficiencyOne"
export LEAN_PATH="$OUT:${LEAN_PATH}"
for f in Defs Basic Lemma2 Theorem1; do
  echo "== building RequestProject/$f.lean (prerequisite)"
  lean -o "$OUT/RequestProject/$f.olean" "RequestProject/$f.lean"
done
for f in Defs Section2FixedPointBound AffineModel Section3PositiveFixedGap Section4Rigidity MainTheorem; do
  echo "== building DeficiencyOne/$f.lean"
  lean -o "$OUT/DeficiencyOne/$f.olean" "DeficiencyOne/$f.lean"
done
echo "== ok (warnings above are the intended 'sorry's of the not-yet-proved statements)"
