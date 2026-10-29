/-
# Lakefile for the Fixed Points and Rigidity Project

This is the configuration file for the Lean 4 build system (Lake).
-/

import Lake
open Lake DSL

package fixedPointsPrimePower {
  -- Add package configuration options here
}

lean_lib FixedPointsPrimePower {
  -- Add library configuration options here
  roots := #[.]
  globs := #[
    "Defs.lean",
    "MainTheorems.lean", 
    "Section2.lean",
    "Section3.lean",
    "Section4.lean"
  ]
}

@[default_target]
lean_exe run {
  root := `Main
}

-- Dependencies
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
