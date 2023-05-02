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

lemma tr132 {a b c : point} : triangle a b c ↔ triangle a c b := by
  constructor; all_goals dsimp [triangle]; rw [col132]; tauto
lemma tr213 {a b c : point} : triangle a b c ↔ triangle b a c := by
  constructor; all_goals dsimp [triangle]; rw [col213]; tauto
lemma tr231 {a b c : point} : triangle a b c ↔ triangle b c a := by
  constructor; all_goals dsimp [triangle]
  rw [col231]; tauto
  rw [← col231]; tauto
lemma tr312 {a b c : point} : triangle a b c ↔ triangle c a b := by
  constructor; all_goals dsimp [triangle]
  rw [col312]; tauto
  rw [← col312]; tauto
lemma tr321 {a b c : point} : triangle a b c ↔ triangle c b a := by
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
  |`(conv| area_nf) => withMainContext do
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
  |`(conv| colinear_nf) => withMainContext do
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
  |`(conv| triangle_nf) => withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      let arg3 := Lean.Expr.getArg! tgt 3
      if lte arg1 arg2 && lte arg2 arg3 then
        evalTactic (← `(tactic| skip )) -- abc
      else if lte arg1 arg3 && lte arg3 arg2 then
        evalTactic (← `(tactic| rw [@tr132 _ _ _] )) -- acb
      else if lte arg2 arg1 && lte arg1 arg3 then
        evalTactic (← `(tactic| rw [@tr213 _ _ _] )) -- bac
      else if lte arg3 arg1 && lte arg1 arg2 then
        evalTactic (← `(tactic| rw [@tr312 _ _ _] )) -- bca
      else if lte arg2 arg3 && lte arg3 arg1 then
        evalTactic (← `(tactic| rw [@tr231 _ _ _] )) -- cab
      else if lte arg3 arg2 && lte arg2 arg1 then
        evalTactic (← `(tactic| rw [@tr321 _ _ _] )) -- cba

/-- ## Conv tactic `length_nf`
A conv tactic for permuting the variables in an `length` expression. A building block for the `perm` tactic.
 -/
syntax "length_nf" : conv
elab_rules : conv
  |`(conv| length_nf) => withMainContext do
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
  |`(conv| angle_nf) => withMainContext do
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
  |`(conv| sameside_nf) => withMainContext do
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
  |`(conv| diffside_nf) => withMainContext do
      let tgt ← instantiateMVars (← Conv.getLhs)
      let arg1 := Lean.Expr.getArg! tgt 1
      let arg2 := Lean.Expr.getArg! tgt 2
      if lte arg1 arg2 then
        evalTactic (← `(tactic| skip ))
      else
        evalTactic (← `(tactic| rw [@ds21 _ _] ))

/-- ## Tactic perm
A custom experimental tactic for permuting the variables in geometric primitives. The ordering is the one in which the variables are introduced, so it is not necessarily lexigraphic in general.

Usage:
- `perm` permutes the variables in the goal
- `perm at h` permutes the variables in hypothesis h
- `perm at *` permutes the variables in the goal and all hypotheses
All of these variants also internally try to use `assumption` or `exact h`.
 -/
syntax "perm" ("only [" ident "]")? ("at" ident)? ("at *")? : tactic
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
      try assumption
    ))
  | `(tactic| perm only [area]) => `(tactic|
    (
      try conv in (occs := *) area _ _ _ => all_goals area_nf
      try assumption
    ))
  | `(tactic| perm only [colinear]) => `(tactic|
    (
      try conv in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try assumption
    ))
  | `(tactic| perm only [triangle]) => `(tactic|
    (
      try conv in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try assumption
    ))
  | `(tactic| perm only [length]) => `(tactic|
    (
      try conv in (occs := *) length _ _ => all_goals length_nf
      try assumption
    ))
  | `(tactic| perm only [angle]) => `(tactic|
    (
      try conv in (occs := *) angle _ _ _ => all_goals angle_nf
      try assumption
    ))
  | `(tactic| perm only [sameside]) => `(tactic|
    (
      try conv in (occs := *) sameside _ _ _ => all_goals sameside_nf
      try assumption
    ))
  | `(tactic| perm only [diffside]) => `(tactic|
    (
      try conv in (occs := *) diffside _ _ _ => all_goals diffside_nf
      try assumption
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
      try exact $h
    ))
  | `(tactic| perm only [area] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) area _ _ _ => all_goals area_nf
      try exact $h
    ))
  | `(tactic| perm only [colinear] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try exact $h
    ))
  | `(tactic| perm only [triangle] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try exact $h
    ))
  | `(tactic| perm only [length] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) length _ _ => all_goals length_nf
      try exact $h
    ))
  | `(tactic| perm only [angle] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) angle _ _ _ => all_goals angle_nf
      try exact $h
    ))
  | `(tactic| perm only [sameside] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) sameside _ _ _ => all_goals sameside_nf
      try exact $h
    ))
  | `(tactic| perm only [diffside] at $h) => `(tactic|
    (
      try conv at $h in (occs := *) diffside _ _ _ => all_goals diffside_nf
      try exact $h
    ))

elab_rules: tactic
  | `(tactic| perm at *) => withMainContext do
      evalTactic (← `(tactic| perm))
      for ldecl in ← getLCtx do
        let name := mkIdent ldecl.userName
        if !ldecl.isImplementationDetail then evalTactic (← `(tactic| perm at $name))
  | `(tactic| perm only [$perm_type] at *) => withMainContext do
      evalTactic (← `(tactic| perm only [$perm_type]))
      for ldecl in ← getLCtx do
        let name := mkIdent ldecl.userName
        if !ldecl.isImplementationDetail then evalTactic (← `(tactic| perm only [$perm_type] at $name))
