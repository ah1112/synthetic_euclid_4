import SyntheticEuclid4
open incidence_geometry
variable [i: incidence_geometry]

lemma ar132 {a b c : point} : area a b c = area a c b
  := by exact (area_invariant a b c).2
lemma ar312 {a b c : point} : area a b c = area c a b
  := by exact (area_invariant a b c).1
lemma ar231 {a b c : point} : area a b c = area b c a
  := by rw [(area_invariant a b c).1]; rw [(area_invariant c a b).1]
lemma ar213 {a b c : point} : area a b c = area b a c
  := by rw [(area_invariant a b c).2]; rw [(area_invariant a c b).1]
lemma ar321 {a b c : point} : area a b c = area c b a
  := by rw [(area_invariant a b c).2]; rw [(area_invariant c b a).1]

/-- ## Tactic perm
A custom experimental tactic for rewriting the order of operands, currently only working for triangle areas.

Usage (partially mimicking the `rw` syntax):
- `perm` tries all possible permutations of the goal
- `perm at h` tries all possible permutations of hypothesis h
- `perm [213]` tries to swap the first two arguments of the goal
- `perm [213] at h` tries to swap the first two arguments of hypothesis h
- `[←213]` can be used instead of `[213]`, targetting the other side of equality
- `perm 2` tries to rewrite the first two terms of the goal
- `perm [213] 2` performs the rewrite on the second term of the goal
- `perm [213] 2 at h` performs the rewrite on the second term of h
 -/
-- syntax wildArg := ident <|> Lean.Parser.Tactic.locationHyp
syntax "perm " "["? ("←"?num),* "]"? (num)? ("at" Lean.Parser.Tactic.locationHyp)? ("then" Lean.Parser.Tactic.tacticSeq)? : tactic

macro_rules
-- explicit versions
  | `(tactic| perm [132]) => `(tactic| try rw [@ar132 _ _ _]; try assumption)
  | `(tactic| perm [312]) => `(tactic| try rw [@ar312 _ _ _]; try assumption)
  | `(tactic| perm [231]) => `(tactic| try rw [@ar231 _ _ _]; try assumption)
  | `(tactic| perm [213]) => `(tactic| try rw [@ar213 _ _ _]; try assumption)
  | `(tactic| perm [321]) => `(tactic| try rw [@ar321 _ _ _]; try assumption)

-- TODO: generalize the type of h and use exact instead of assumption
  | `(tactic| perm [132] at $h) => `(tactic| try rw [@ar132 _ _ _] at $h; try assumption)
  | `(tactic| perm [312] at $h) => `(tactic| try rw [@ar312 _ _ _] at $h; try assumption)
  | `(tactic| perm [231] at $h) => `(tactic| try rw [@ar231 _ _ _] at $h; try assumption)
  | `(tactic| perm [213] at $h) => `(tactic| try rw [@ar213 _ _ _] at $h; try assumption)
  | `(tactic| perm [321] at $h) => `(tactic| try rw [@ar321 _ _ _] at $h; try assumption)

-- implicit versions
  | `(tactic| perm) => `(tactic|
  {
   try {perm [132]}
   try {perm [312]}
   try {perm [231]}
   try {perm [213]}
   try {perm [321]}
  })

  | `(tactic| perm then $t) => `(tactic|
  {
   try {perm [132]; try $t}
   try {perm [312]; try $t}
   try {perm [231]; try $t}
   try {perm [213]; try $t}
   try {perm [321]; try $t}
  })

  | `(tactic| perm at $h) => `(tactic|
  {
    -- TODO: rw of h, perhaps with Lean.Parser.Tactic.rwRule?
   try {perm [132] at $h}
   try {perm [312] at $h}
   try {perm [231] at $h}
   try {perm [213] at $h}
   try {perm [321] at $h}
  })

  | `(tactic| perm at $h then $t) => `(tactic|
  {
    -- TODO: rw of h, perhaps with Lean.Parser.Tactic.rwRule?
   try {perm [132] at $h; try $t}
   try {perm [312] at $h; try $t}
   try {perm [231] at $h; try $t}
   try {perm [213] at $h; try $t}
   try {perm [321] at $h; try $t}
  })

-- subexpression versions
  | `(tactic| perm [$a] $n) => `(tactic| conv => lhs; arg $n; tactic => perm [$a])
  | `(tactic| perm [$a] 2 at $h) => `(tactic| rw [add_comm] at $h; perm [$a] at $h; try rw [add_comm] at $h)
  -- TODO: generalize this by allowing h to be of type ident
  | `(tactic| perm $n) => `(tactic|
  {
  -- TODO : recurse with n-1
   try {perm [132] $n; try perm}
   try {perm [312] $n; try perm}
   try {perm [231] $n; try perm}
   try {perm [213] $n; try perm}
   try {perm [321] $n; try perm}
  })

-- backwards and iterative versions
-- TODO: ← should invoke the backwards rw instead; both should also have a h version
  | `(tactic| perm [←$a]) => `(tactic| apply Eq.symm; perm [$a]; try apply Eq.symm)
  | `(tactic| perm [$a, ←$b]) => `(tactic| perm [$a]; perm [←$b])
  | `(tactic| perm [←$a, $b]) => `(tactic| perm [←$a]; perm [$b])
  | `(tactic| perm [←$a, ←$b]) => `(tactic| perm [←$a]; perm [←$b])
  | `(tactic| perm [$a, $b]) => `(tactic| perm [$a]; perm [$b])
  | `(tactic| perm [$a, $b] at $h) => `(tactic| perm [$a] at $h; perm [$b] at $h)
  | `(tactic| perm [$a, $b, $c] at $h) => `(tactic| perm [$a] at $h; perm [$b] at $h; perm [$c] at $h)
