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

namespace Lean.Elab.Tactic

def lte (a : @& Expr) (b : @& Expr) : Bool :=
  Lean.Expr.lt a b || Lean.Expr.equal a b

/-- ## Conv tactic `perm_nf`
A conv tactic for permuting the variables in a single geometric primitive. A building block for the `perm` tactic.
 -/
syntax "perm_nf" : conv
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
        evalTactic (← `(tactic| rw [@ar132 _ _ _] )) -- acb
      else if lte arg2 arg1 && lte arg1 arg3 then
        evalTactic (← `(tactic| rw [@ar213 _ _ _] )) -- bac
      else if lte arg3 arg1 && lte arg1 arg2 then
        evalTactic (← `(tactic| rw [@ar312 _ _ _] )) -- bca
      else if lte arg2 arg3 && lte arg3 arg1 then
        evalTactic (← `(tactic| rw [@ar231 _ _ _] )) -- cab
      else if lte arg3 arg2 && lte arg2 arg1 then
        evalTactic (← `(tactic| rw [@ar321 _ _ _] )) -- cba

/-- ## Tactic perm
A custom experimental tactic for permuting the variables in geometric primitives. The ordering is the one in which the variables are introduced, so it is not necessarily lexigraphic in general. Currently only working for triangle areas.

Usage:
- `perm` permutes the variables in the goal
- `perm at h` permutes the variables in hypothesis h
- `perm at *` TODO: permutes the variables in the goal and all hypotheses
 -/
syntax "perm" ("at" ident)? : tactic
macro_rules
  | `(tactic| perm) => `(tactic| conv in (occs := *) area _ _ _ => all_goals perm_nf)
  | `(tactic| perm at $h) => `(tactic| conv at $h in (occs := *) area _ _ _ => all_goals perm_nf)
