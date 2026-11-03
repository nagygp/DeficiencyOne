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

# Every file imports `Mathlib`, so the build needs a Mathlib built by the same Lean version as
# the `lean` on PATH.  This script cannot supply one (there is no lakefile to resolve), so say so
# plainly instead of dying on an unbound variable under `set -u`.
if [ -z "${LEAN_PATH:-}" ]; then
  cat >&2 <<'MSG'
error: LEAN_PATH is not set, and every file here imports `Mathlib`.

Set it to a Mathlib built by the same Lean as the `lean` on PATH, e.g.

    export LEAN_PATH="$(cd ~/mathlib4 && lake env printenv LEAN_PATH)"

See HOWTO.md: "On the Open Math OS VM" (LEAN_PATH is already set there) and
"Using Lean 4.33 locally" for fetching a matching Mathlib with `lake exe cache get`.
MSG
  exit 1
fi

mkdir -p "$OUT/RequestProject" "$OUT/DeficiencyOne"
export LEAN_PATH="$OUT${LEAN_PATH:+:$LEAN_PATH}"
for f in Defs Basic Lemma2 Theorem1; do
  echo "== building RequestProject/$f.lean (prerequisite)"
  lean -o "$OUT/RequestProject/$f.olean" "RequestProject/$f.lean"
done
for f in Defs Section2FixedPointBound AffineModel Section3PositiveFixedGap Section4Rigidity MainTheorem; do
  echo "== building DeficiencyOne/$f.lean"
  lean -o "$OUT/DeficiencyOne/$f.olean" "DeficiencyOne/$f.lean"
done
# Each file is compiled with the default linter set and emits no warnings except the five
# intentional `sorry`s (Theorem 11 and Lemma 12 in §3, Lemma 14 and Theorems 15, 17 in §4) —
# those still print `declaration uses 'sorry'`, on purpose: the inventory is in README.md.
# Any other warning printed here is a regression.
echo "== ok (only the five intended 'sorry' warnings)"
