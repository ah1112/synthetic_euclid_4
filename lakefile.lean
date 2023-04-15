import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package synthetic_euclid_4

@[default_target]
lean_lib SyntheticEuclid4
