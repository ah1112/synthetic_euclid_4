import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"
package synthetic_euclid_4

@[default_target]
lean_lib SyntheticEuclid4
