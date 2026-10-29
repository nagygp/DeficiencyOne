/-
# Lakefile for the Fixed Points and Rigidity Project

This is the configuration file for the Lean 4 build system (Lake).
-/

import Lake
open Lake DSL

package fixedPointsPrimePower {
  -- Add package configuration options here
}

@[default_target]
lean_lib FixedPointsPrimePower {
  -- Add library configuration options here
  roots := #[`Defs, `MainTheorems, `Section2, `Section3, `Section4, `Theorem1]
  globs := #[
    .one `Defs,
    .one `MainTheorems,
    .one `Section2,
    .one `Section3,
    .one `Section4,
    .one `Theorem1,
    .submodules `Theorem2,
    .submodules `Theorem3
  ]
}

-- Dependencies
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"
