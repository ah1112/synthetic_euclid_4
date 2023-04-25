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
A custom experimental tactic for lexicographically permuting the order of operands, currently only working for triangle areas.

Usage:
- `perm` lexicographically permutes the goal
- `perm at h` lexicographically permutes hypothesis h
- `perm [213]` permutes the first two arguments of the goal
 -/
syntax "perm" "["? ("←"?num),* "]"? ("at" ident)? : tactic

macro_rules
-- explicit versions
  | `(tactic| perm [132]) => `(tactic| rw [@ar132 _ _ _])
  | `(tactic| perm [312]) => `(tactic| rw [@ar312 _ _ _])
  | `(tactic| perm [231]) => `(tactic| rw [@ar231 _ _ _])
  | `(tactic| perm [213]) => `(tactic| rw [@ar213 _ _ _])
  | `(tactic| perm [321]) => `(tactic| rw [@ar321 _ _ _])

namespace Lean.Elab.Tactic

def lte (a : @& Expr) (b : @& Expr) : Bool :=
  Lean.Expr.lt a b || Lean.Expr.equal a b

syntax (name := perm_nf) "perm_nf" : conv
elab_rules : conv 
  |`(conv| perm_nf) => do
  withMainContext do
    let tgt ← instantiateMVars (← Conv.getLhs)
    let arg1 := Lean.Expr.getArg! tgt 1
    let arg2 := Lean.Expr.getArg! tgt 2
    let arg3 := Lean.Expr.getArg! tgt 3
    if lte arg1 arg2 && lte arg2 arg3 then
      evalTactic (← `(tactic| try rfl )) -- abc
    else if lte arg1 arg3 && lte arg3 arg2 then
      evalTactic (← `(tactic| perm [132] )) -- acb
    else if lte arg2 arg1 && lte arg1 arg3 then
      evalTactic (← `(tactic| perm [213] )) -- bac
    else if lte arg3 arg1 && lte arg1 arg2 then
      evalTactic (← `(tactic| perm [312] )) -- bca
    else if lte arg2 arg3 && lte arg3 arg1 then
      evalTactic (← `(tactic| perm [231] )) -- cab
    else if lte arg3 arg2 && lte arg2 arg1 then
      evalTactic (← `(tactic| perm [321] )) -- cba

macro_rules
-- implicit versions
  | `(tactic| perm) => `(tactic|
  {
    conv =>
      lhs
      args
      all_goals perm_nf
    
    conv =>
      rhs
      args
      all_goals perm_nf
  })

syntax "perm'" : tactic
macro_rules
  | `(tactic| perm') => `(tactic|
  {
    conv =>
      args
      all_goals try {perm_nf}
  })