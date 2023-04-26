import SyntheticEuclid4.axioms
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

lemma col213 : colinear a b c ↔ colinear b a c := by
  constructor
  all_goals
    intro h
    obtain ⟨ L, hL ⟩ := h
    use L
    exact and_left_comm.mp hL
lemma col231 : colinear a b c ↔ colinear b c a := by
  constructor
  all_goals
    intro h
    obtain ⟨ L, hL ⟩ := h
    use L
  exact and_rotate.mp hL
  exact and_rotate.mpr hL
lemma col132 : colinear a b c ↔ colinear a c b := by conv => rhs; rw [col213]; rw [col231]
lemma col312 : colinear a b c ↔ colinear c a b := by conv => lhs; rw [← col231]
lemma col321 : colinear a b c ↔ colinear c b a := by conv => rhs; rw [col231]; rw [col213]

lemma tri132 {a b c : point} : triangle a b c ↔ triangle a c b := by
  constructor; all_goals dsimp [triangle]; rw [col132]; tauto
lemma tri213 {a b c : point} : triangle a b c ↔ triangle b a c := by
  constructor; all_goals dsimp [triangle]; rw [col213]; tauto
lemma tri231 {a b c : point} : triangle a b c ↔ triangle b c a := by
  constructor; all_goals dsimp [triangle]
  rw [col231]; tauto
  rw [← col231]; tauto
lemma tri312 {a b c : point} : triangle a b c ↔ triangle c a b := by
  constructor; all_goals dsimp [triangle]
  rw [col312]; tauto
  rw [← col312]; tauto
lemma tri321 {a b c : point} : triangle a b c ↔ triangle c b a := by
  constructor; all_goals dsimp [triangle]; rw [col321]; tauto

lemma ss21 {a b : point} {L : line}: sameside a b L ↔ sameside b a L := by
  constructor; repeat exact sameside_symm

lemma ds21 {a b : point} {L : line}: diffside a b L ↔ diffside b a L := by
  constructor
  all_goals
    intro h
    obtain ⟨ naL, nbL, nss ⟩ := h
    rw [ss21] at nss
    exact ⟨ nbL, naL, nss ⟩


namespace Lean.Elab.Tactic

def lte (a : @& Expr) (b : @& Expr) : Bool :=
  Lean.Expr.lt a b || Lean.Expr.equal a b

/-- ## Conv tactic `area_nf`
A conv tactic for permuting the variables in an `area` expression. A building block for the `perm` tactic.
 -/
syntax "area_nf" : conv
elab_rules : conv
  |`(conv| area_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      let arg3 := Lean.Expr.getArg! tgt 3
      if lte arg1 arg2 && lte arg2 arg3 then
        evalTactic (← `(tactic| skip )) -- abc
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

/-- ## Conv tactic `colinear_nf`
A conv tactic for permuting the variables in an `colinear` expression. A building block for the `perm` tactic.
 -/
syntax "colinear_nf" : conv
elab_rules : conv
  |`(conv| colinear_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      let arg3 := Lean.Expr.getArg! tgt 3
      if lte arg1 arg2 && lte arg2 arg3 then
        evalTactic (← `(tactic| skip )) -- abc
      else if lte arg1 arg3 && lte arg3 arg2 then
        evalTactic (← `(tactic| rw [@col132 _ _ _] )) -- acb
      else if lte arg2 arg1 && lte arg1 arg3 then
        evalTactic (← `(tactic| rw [@col213 _ _ _] )) -- bac
      else if lte arg3 arg1 && lte arg1 arg2 then
        evalTactic (← `(tactic| rw [@col312 _ _ _] )) -- bca
      else if lte arg2 arg3 && lte arg3 arg1 then
        evalTactic (← `(tactic| rw [@col231 _ _ _] )) -- cab
      else if lte arg3 arg2 && lte arg2 arg1 then
        evalTactic (← `(tactic| rw [@col321 _ _ _] )) -- cba

/-- ## Conv tactic `triangle_nf`
A conv tactic for permuting the variables in an `triangle` expression. A building block for the `perm` tactic.
 -/
syntax "triangle_nf" : conv
elab_rules : conv
  |`(conv| triangle_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      let arg3 := Lean.Expr.getArg! tgt 3
      if lte arg1 arg2 && lte arg2 arg3 then
        evalTactic (← `(tactic| skip )) -- abc
      else if lte arg1 arg3 && lte arg3 arg2 then
        evalTactic (← `(tactic| rw [@tri132 _ _ _] )) -- acb
      else if lte arg2 arg1 && lte arg1 arg3 then
        evalTactic (← `(tactic| rw [@tri213 _ _ _] )) -- bac
      else if lte arg3 arg1 && lte arg1 arg2 then
        evalTactic (← `(tactic| rw [@tri312 _ _ _] )) -- bca
      else if lte arg2 arg3 && lte arg3 arg1 then
        evalTactic (← `(tactic| rw [@tri231 _ _ _] )) -- cab
      else if lte arg3 arg2 && lte arg2 arg1 then
        evalTactic (← `(tactic| rw [@tri321 _ _ _] )) -- cba

/-- ## Conv tactic `length_nf`
A conv tactic for permuting the variables in an `length` expression. A building block for the `perm` tactic.
 -/
syntax "length_nf" : conv
elab_rules : conv
  |`(conv| length_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      if lte arg1 arg2 then
        evalTactic (← `(tactic| skip ))
      else
        evalTactic (← `(tactic| rw [@length_symm _ _] ))

/-- ## Conv tactic `angle_nf`
A conv tactic for permuting the variables in an `angle` expression. A building block for the `perm` tactic.
 -/
syntax "angle_nf" : conv
elab_rules : conv
  |`(conv| angle_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg3 := Lean.Expr.getArg! tgt 3
      if lte arg1 arg3 then
        evalTactic (← `(tactic| skip ))
      else
        evalTactic (← `(tactic| rw [@angle_symm _ _] ))

/-- ## Conv tactic `sameside_nf`
A conv tactic for permuting the variables in an `sameside` expression. A building block for the `perm` tactic.
 -/
syntax "sameside_nf" : conv
elab_rules : conv
  |`(conv| sameside_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      if lte arg1 arg2 then
        evalTactic (← `(tactic| skip ))
      else
        evalTactic (← `(tactic| rw [@ss21 _ _] ))

/-- ## Conv tactic `diffside_nf`
A conv tactic for permuting the variables in an `diffside` expression. A building block for the `perm` tactic.
 -/
syntax "diffside_nf" : conv
elab_rules : conv
  |`(conv| diffside_nf) => do
    withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      if lte arg1 arg2 then
        evalTactic (← `(tactic| skip ))
      else
        evalTactic (← `(tactic| rw [@ds21 _ _] ))

/-- ## Tactic perm
A custom experimental tactic for permuting the variables in geometric primitives. The ordering is the one in which the variables are introduced, so it is not necessarily lexigraphic in general. Currently only working for triangle areas.

Usage:
- `perm` permutes the variables in the goal
- `perm at h` permutes the variables in hypothesis h
- `perm at *` TODO: permutes the variables in the goal and all hypotheses
 -/
syntax "perm" ("at" ident)? ("*")? : tactic
macro_rules
  | `(tactic| perm) => `(tactic|
    (
      try conv in (occs := *) area _ _ _ => all_goals area_nf
      try conv in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try conv in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try conv in (occs := *) length _ _ => all_goals length_nf
      try conv in (occs := *) angle _ _ _ => all_goals angle_nf
      try conv in (occs := *) sameside _ _ _ => all_goals sameside_nf
      try conv in (occs := *) diffside _ _ _ => all_goals diffside_nf
    ))
  | `(tactic| perm at $h) => `(tactic|
    (
      try conv at $h in (occs := *) area _ _ _ => all_goals area_nf
      try conv at $h in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try conv at $h in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try conv at $h in (occs := *) length _ _ => all_goals length_nf
      try conv at $h in (occs := *) angle _ _ _ => all_goals angle_nf
      try conv at $h in (occs := *) sameside _ _ _ => all_goals sameside_nf
      try conv at $h in (occs := *) diffside _ _ _ => all_goals diffside_nf
    ))
