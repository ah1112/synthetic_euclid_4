/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.WLOG

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we ...

## Main definitions
* `incidence_geometry` : class containing axioms...

## Main results
* `pythagorean_theorem` : The Pythagorean theorem
## Tags
synthetic geometry, Euclid elements
-/

universe u1 u2 u3
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(center_circle : point → circle → Prop)
(on_circle : point → circle → Prop)
(in_circle : point → circle → Prop)
(lines_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circles_inter : circle → circle → Prop)
(length : point → point → ℝ)
(angle : point → point → point → ℝ)
(rightangle : ℝ)
(area : point → point → point → ℝ)

(more_pts : ∀ (S : Set point), S.Finite → ∃ (a : point), a ∉ S)
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
(diffside_of_not_online : ∀ {L : line}, ∀ {a : point}, ¬online a L →
    ∃ (b : point), ¬online b L ∧ ¬sameside a b L)
(line_of_pts : ∀ (a b : point), ∃ (L :line), online a L ∧ online b L)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ on_circle b α)
(pt_of_lines_inter : ∀ {L M : line}, lines_inter L M →
  ∃ (a : point), online a L ∧ online a M)
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point),  a ≠ b ∧ online a L ∧ online b L ∧ on_circle a α ∧ on_circle b α )
(pt_on_circle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  ¬on_circle c α →in_circle b α → ¬in_circle c α →
  ∃ (a : point), B b a c ∧ on_circle a α)
(pt_oncircle_of_inside_ne : ∀ {a b : point}, ∀ {α : circle}, a ≠ b → in_circle b α →
  ∃ (c : point), B a b c ∧ on_circle c α)
(pts_of_circles_inter : ∀ {α β : circle}, circles_inter α β →
  ∃ (a b : point), a≠ b∧ on_circle a α ∧ on_circle a β ∧ on_circle b α ∧ on_circle b β )
(pt_sameside_of_circles_inter : ∀ {b c d : point}, ∀ {L : line}, ∀ {α β : circle},
  online c L → online d L →¬online b L  → center_circle c α → center_circle d β →circles_inter α β
  →  ∃ (a : point), sameside a b L∧ on_circle a α ∧  on_circle a β )
(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, center_circle a α → center_circle b α →
  a = b)
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, center_circle a α → in_circle a α)
(not_on_circle_of_inside : ∀ {a : point}, ∀ {α : circle}, in_circle a α → ¬on_circle a α)
(B_symm : ∀ {a b c : point}, B a b c → B c b a )
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L →  B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)
(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L → ¬online c L →
  ¬sameside a b L → sameside a c L ∨ sameside b c L)
(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L → sameside a b L)
(sameside_of_B_not_online_2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L → ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, a ≠ b → b ≠ c → a ≠ c → L ≠ M → online a L → 
  online b L → online c L → online b M → ¬sameside a c M → B a b c)
(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, a≠ b → online a L → online a M → online a N → online b L →
  online c M → online d N → ¬online d M → sameside c d L → ¬sameside b d M →
  sameside b c N)
(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle },b ≠ c → online a L → online b L → online c L
  → on_circle b α → on_circle c α → in_circle a α →   B b a c)
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {L : line}, ∀ {α β : circle},  c ≠ d→ α ≠ β →  online a L
  → online b L  → on_circle c α → on_circle c β → on_circle d α → on_circle d β → center_circle a α → center_circle b β →
  circles_inter α β → ¬sameside c d L)
(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, online a M → online b M → ¬sameside a b L →
  lines_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle},¬sameside a b L → on_circle a α ∨ in_circle a α→
 on_circle b α ∨ in_circle b α  →  line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, online a L → in_circle a α →  line_circle_inter L α)
(circles_inter_of_inside_on_circle : ∀ {a b : point}, ∀ {α β : circle}, on_circle b α → on_circle a β → in_circle a α →  in_circle b β →
  circles_inter α β)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_symm : ∀ (a b : point), length a b = length b a)
(angle_symm : ∀ (a b c : point), angle a b c = angle c b a)
(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(area_nonneg : ∀ (a b c : point), 0 ≤ area a b c)
(degenerate_area : ∀ (a b : point), area a a b = 0)
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 →
  length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1)
(length_sum_of_B : ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(on_circle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle},  center_circle a α → on_circle b α → 
  (length a b = length a c ↔ on_circle c α))
(in_circle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α → 
  (length a c < length a b ↔ in_circle c α))
(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, a ≠ b → a ≠ c → online a L → online b L → online a M
  → online c M → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L → ¬online d L → B a c b →
  (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → online a L → online b L → online b1 L →
  online a M → online c M → online c1 M →  ¬B b a b1 → ¬B c a c1 → angle b a c = angle b1 a1 c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line},b ≠ c → online a L → online b L → online b M → online c M →
  online c N → online d N →  sameside a d M → angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)
(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a b c ↔ area d a b + area d c b = area d a c))
(SAS_iff_SSS : ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f)) --Euclid Prop 4,8

variable [i : incidence_geometry]
open incidence_geometry
-------------------------------------------------- Definitions -------------------------------------
def diffside (a b : point) (L : line) := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L
--3/28/23
def out_circle (a : point) (α : circle) := ¬on_circle a α ∧ ¬in_circle a α

def colinear (a b c : point) := ∃ L : line, online a L ∧ online b L ∧ online c L

def triangle (a b c : point) := ¬colinear a b c

def eq_tri (a b c : point) := triangle a b c ∧ length a b = length a c ∧ length b a = length b c
  ∧ length c a = length c b

def iso_tri (a b c : point) := triangle a b c ∧ length a b = length a c
-------------------------------------------------- new  API --------------------------------------------'
  theorem online_of_line (L : line) : ∃ (a : point), online a L := by 
rcases more_pts ∅ Set.finite_empty with ⟨a, -⟩; exact Classical.by_cases 
 (fun aL => by use a; exact aL) (fun aL => 
by rcases diffside_of_not_online aL with ⟨b, -, abL⟩; rcases line_of_pts a b with ⟨M, aM, bM⟩; 
   rcases pt_of_lines_inter (lines_inter_of_not_sameside aM bM abL) with ⟨c, cL, -⟩; exact ⟨c, cL⟩)

theorem online_ne_of_line (L : line) : ∃ (a b : point), a ≠ b ∧ online a L ∧ online b L := by
  rcases online_of_line L with ⟨a, aL⟩; rcases more_pts {a} (Set.finite_singleton a) with ⟨b, hb⟩;
  rcases circle_of_ne $ ne_of_mem_of_not_mem (Set.mem_singleton a) hb with ⟨α, acen, -⟩;
  rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online aL
  (inside_circle_of_center acen)) with ⟨c, d, cd, cL, dL, -, -⟩; exact ⟨c, d, cd, cL, dL⟩

lemma len_pos_of_nq (ab : a ≠ b) : 0 < length a b :=
  (Ne.symm (not_imp_not.mpr length_eq_zero_iff.mp ab)).le_iff_lt.mp (length_nonneg a b)

theorem ne_of_ne_len (ab : a ≠ b) (ab_cd : length a b = length c d) : c ≠ d :=
  fun ac => by sorry --linarith[length_eq_zero_iff.mpr ac, len_pos_of_nq ab]

theorem ne_of_ne_len' (cd : c ≠ d) (ab_cd : length a b = length c d) : a ≠ b := --3/28/23
  ne_of_ne_len cd (ab_cd.symm)

theorem length_sum_perm_of_B (Babc : B a b c) : 0 < length a b ∧ 0 < length b a ∧ 0 < length b c
  ∧ 0 < length c b ∧ 0 < length a c ∧ 0 < length c a ∧ length a b + length b c = length a c ∧
  length b a + length b c = length a c ∧ length b a + length c b = length a c ∧
  length b a + length b c = length c a ∧ length b a + length c b = length c a ∧
  length a b + length c b = length a c ∧ length a b + length b c = length c a ∧
  length a b + length c b = length c a := by sorry
-- ⟨len_pos_of_nq (ne_12_of_B Babc), by linarith[length_symm a b,
-- len_pos_of_nq (ne_12_of_B Babc)], len_pos_of_nq (ne_23_of_B Babc), by linarith[length_symm b c,
-- len_pos_of_nq (ne_23_of_B Babc)], len_pos_of_nq (ne_13_of_B Babc), by linarith[length_symm a c,
-- len_pos_of_nq (ne_13_of_B Babc)], by repeat {split}; repeat {linarith[length_sum_of_B Babc,
-- length_symm a b, length_symm a c, length_symm b c]}⟩

theorem length_perm_of_3pts (a b c : point) : length a b = length b a ∧ length a c = length c a ∧
  length b c = length c b := ⟨length_symm a b, length_symm a c, length_symm b c⟩

theorem not_online_of_line (L : line) : ∃ (a : point), ¬online a L := by sorry
  -- by rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩; rcases circle_of_ne bc with ⟨α, bα, cα⟩;
  -- rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩; rcases pts_of_circles_inter
  -- (circles_inter_of_inside_on_circle cα bβ (inside_circle_of_center bα) (inside_circle_of_center
  -- cβ)) with ⟨a, -, -, aα, aβ, -, -⟩; have bc_ba := (on_circle_iff_length_eq bα cα).mpr aα;
  -- have cb_ca := (on_circle_iff_length_eq cβ bβ).mpr aβ; exact ⟨a, λ aL, ((by push_neg; repeat
  -- {split}; repeat {exact (λ Bet, by linarith[length_sum_perm_of_B Bet])}) : ¬ (B b c a ∨ B c b a ∨
  -- B b a c)) (B_of_three_online_ne bc (ne_of_ne_len bc bc_ba)(ne_of_ne_len bc.symm cb_ca) bL cL aL)⟩

theorem online_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ (c : point) (L : line), online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ ¬online c L := by 
rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases not_online_of_line L with ⟨d, dL⟩;
  rcases pt_sameside_of_circles_inter aL bL dL aα bβ αβ with ⟨c, cdL, cα, cβ⟩;
  exact ⟨c, L, aL, bL, cα, cβ, not_online_of_sameside cdL⟩

theorem not_sameside_symm (abL : ¬sameside a b L) : ¬sameside b a L := fun baL =>
  abL (sameside_symm baL)

lemma diffside_symm (abL : diffside a b L) : diffside b a L :=
  ⟨abL.2.1, abL.1, (not_sameside_symm abL.2.2)⟩

theorem diffside_of_sameside_diffside (abL : sameside a b L) (acL : diffside a c L) :
  diffside b c L := by 
by_contra h; unfold diffside at h; push_neg at h; exact acL.2.2
 (sameside_trans (sameside_symm abL) (h (not_online_of_sameside (sameside_symm abL)) acL.2.1))

theorem diffside_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ (c d : point) (L : line), online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ on_circle d α ∧ on_circle d β ∧ diffside c d L := by 
rcases online_of_circles_inter aα bβ αβ with ⟨c, L, aL, bL, cα, cβ, cL⟩;
rcases diffside_of_not_online cL with ⟨e, eL, ceL⟩; rcases pt_sameside_of_circles_inter aL bL eL
 aα bβ αβ with ⟨d, deL, dα, dβ⟩; exact ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, diffside_symm
 (diffside_of_sameside_diffside (sameside_symm deL) ⟨eL, cL, not_sameside_symm ceL⟩)⟩

theorem online_of_col_online (ab : a ≠ b) (aL : online a L) (bL : online b L) 
  (col_abc : colinear a b c) : online c L := 
by rcases col_abc with ⟨L, aM, bM, cM⟩; rwa [line_unique_of_pts ab aM bM aL bL] at cM
--2023/4/8 (changed)
theorem triangle_of_ne_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L) :
  triangle a b c := fun col => by exact cL (online_of_col_online ab aL bL col)
--2023/4/8
theorem online_3_of_triangle (aL : online a L) (bL : online b L) (tri_abc : triangle a b c) : 
  ¬online c L := fun cL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_1_of_triangle (bL : online b L) (cL : online c L) (tri_abc : triangle a b c) : 
  ¬online a L := fun aL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_2_of_triangle (aL : online a L) (cL : online c L) (tri_abc : triangle a b c) : 
  ¬online b L := fun bL => tri_abc ⟨L, aL, bL, cL⟩ 

theorem eq_tri_of_length_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L)
  (ab_ac : length a b = length a c) (bc_ba : length b c = length b a) : eq_tri a b c :=
⟨triangle_of_ne_online ab aL bL cL, by repeat {constructor}; sorry⟩ -- linarith[length_perm_of_3pts a b c]⟩
--3/23/23
theorem B_circ_of_ne (ab : a ≠ b) (bc : b ≠ c) : ∃ (d : point) (α : circle), B a b d ∧
  center_circle b α ∧ on_circle c α ∧ on_circle d α := by
rcases circle_of_ne bc with ⟨α, bα, cα⟩; rcases pt_oncircle_of_inside_ne ab
 (inside_circle_of_center bα) with ⟨d, Babd, dα⟩; exact ⟨d, α, Babd, bα, cα, dα⟩

theorem online_of_eq (ab : a = b) (aL : online a L) : online b L := by rwa [ab] at aL

theorem online_of_eq' (ab : a = b) (bL : online b L) : online a L := by rwa [ab.symm] at bL
--2023/4/7
theorem ne_12_of_tri (tri: triangle a b c) : a ≠ b :=
  fun ac => by rcases line_of_pts a c with ⟨L, aL, cL⟩; exact tri ⟨L, aL, online_of_eq ac aL, cL⟩

theorem ne_23_of_tri (tri: triangle a b c) : b ≠ c :=
  fun bc => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq bc bL⟩

theorem ne_32_of_tri (tri : triangle a b c) : c ≠ b := fun cb => (ne_23_of_tri tri) cb.symm

theorem ne_13_of_tri (tri : triangle a b c) : a ≠ c :=
  fun ac => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq ac aL⟩

theorem ne_31_of_tri (tri : triangle a b c) : c ≠ a := fun ca => (ne_13_of_tri tri) ca.symm

theorem incirc_of_lt (aα : center_circle a α) (bα : on_circle b α)
  (ac_ab : length a c < length a b) : in_circle c α := (in_circle_iff_length_lt aα bα).mp ac_ab

theorem B_circ_out_of_B (ab : a ≠ b) (Bacd : B a c d) (ab_ac : length a b = length a c) :
  ∃ (e : point) (α : circle), B a b e ∧ center_circle a α ∧ on_circle d α ∧ on_circle e α := by
rcases circle_of_ne (ne_13_of_B Bacd) with ⟨α, aα, dα⟩; 
rcases pt_oncircle_of_inside_ne ab (incirc_of_lt aα dα (by linarith[length_sum_perm_of_B Bacd] : 
length a b < length a d)) with ⟨e, Babe, eα⟩; exact ⟨e, α, Babe, aα, dα, eα⟩

theorem length_eq_of_oncircle (aα : center_circle a α) (bα : on_circle b α) (cα : on_circle c α) :
   length a b = length a c := (on_circle_iff_length_eq aα bα).mpr cα
--3/28/23
theorem on_circle_of_oncircle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≠ length a c) : ¬on_circle c α := 
fun cα => ab_ac (length_eq_of_oncircle aα bα cα)
--3/28/23
theorem incircle_of_on_circle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≤ length a c) : ¬in_circle c α :=
fun c_in_α => by linarith[(in_circle_iff_length_lt aα bα).mpr c_in_α]

theorem length_eq_of_B_B (Bdbe: B d b e) (Bdaf : B d a f) (da_db : length d a = length d b)
  (de_df : length d e = length d f):
length a f = length b e := by linarith[length_sum_perm_of_B Bdbe, length_sum_perm_of_B Bdaf]

theorem B_oncircle_of_inside_outside (a_in_α : in_circle a α) (b_out_α : out_circle b α) :
  ∃ (c : point), B a c b ∧ on_circle c α :=
pt_on_circle_of_inside_outside b_out_α.1 a_in_α b_out_α.2
--3/28/23
theorem out_circle_of_lt (aα : center_circle a α) (bα : on_circle b α)
  (ab_lt_ac : length a b < length a c) : out_circle c α :=
⟨on_circle_of_oncircle_length aα bα (by linarith), incircle_of_on_circle_length aα bα (by linarith)⟩
--2023/4/5
theorem sss (ab_de : length a b = length d e) (bc_ef : length b c = length e f) 
(ac_df : length a c = length d f) : angle a b c = angle d e f ∧ angle b a c = angle e d f 
  ∧ angle a c b = angle d f e := 
⟨(SAS_iff_SSS (by rwa [length_symm d e, length_symm a b] at ab_de) bc_ef).mpr ac_df, 
(SAS_iff_SSS ab_de ac_df).mpr bc_ef, (SAS_iff_SSS (by rwa [length_symm a c, length_symm d f] 
at ac_df) (by rwa [length_symm b c, length_symm e f] at bc_ef)).mpr ab_de⟩
--2023/4/5
theorem sas (ab_de : length a b = length d e) (ac_df : length a c = length d f) 
(Abac : angle b a c = angle e d f) : length b c = length e f ∧ angle a b c = angle d e f ∧ 
  angle a c b = angle d f e := 
⟨(SAS_iff_SSS ab_de ac_df).1 Abac, (sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).1, 
(sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).2.2⟩ --Euclid I.4
--2023/4/6
  theorem tri132_of_tri123 (tri_abc : triangle a b c) : triangle a c b := 
fun col => by unfold colinear at col; simp_rw [And.comm] at col; exact tri_abc col
--2023/4/8
  theorem tri231_of_tri123 (tri_abc : triangle a b c) : triangle b c a := 
fun col => by rcases col with ⟨L, bL, cL, aL⟩; exact tri_abc ⟨L, aL, bL, cL⟩ 
--2023/4/14
  theorem tri312 (tri_abc : triangle a b c) : triangle c a b := 
    tri231_of_tri123 $ tri231_of_tri123 $ tri_abc
--2023/4/14
  theorem tri213 (tri_abc : triangle a b c) : triangle b a c := 
    tri132_of_tri123 $ tri231_of_tri123 $ tri_abc
 --2023/4/17
  theorem tri321 (tri_abc : triangle a b c) : triangle c b a := tri132_of_tri123 $ tri312 tri_abc
--2023/4/7
theorem area_eq_of_sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
  (Abac_Aedf : angle b a c = angle e d f) : area a b c = area d e f := 
area_eq_of_SSS ab_de ac_df (sas ab_de ac_df Abac_Aedf).1
--2023/4/7
  theorem angle_extension_of_B (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩;
refine angle_extension ((ne_12_of_B Babb1).symm) ((ne_13_of_B Babb1).symm) ac.symm ac.symm aL bL 
  (online_3_of_B Babb1 aL bL) aM cM cM (not_B_of_B Babb1) $ fun Bcac => (ne_13_of_B Bcac) rfl
--2023/4/8
theorem area_add_of_B (Babc : B a b c) (tri_dac : triangle d a c) : 
  area d a b + area d c b = area d a c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; have cL := online_3_of_B Babc aL bL
exact (area_add_iff_B (ne_12_of_B Babc) (ne_23_of_B Babc) (Ne.symm (ne_13_of_B Babc)) aL bL cL
  (online_1_of_triangle aL cL tri_dac)).mp Babc
--2023/4/8
  theorem col_of_area_zero_ne (ab : a ≠ b) (area_abc : area a b c = 0) : colinear a b c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; 
exact ⟨L, aL, bL, (area_zero_iff_online ab aL bL).mp area_abc⟩
--2023/4/8
theorem col_132_of_col (col_123 : colinear a b c) : colinear a c b := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, bL⟩ 
--2023/4/14
theorem col_213_of_col (col_123 : colinear a b c) : colinear b a c := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, bL, aL, cL⟩ 
--2023/4/8
theorem col_134_of_col_123_col_124 (ab : a ≠ b) (col_123 : colinear a b c) 
  (col_124 : colinear a b d) : colinear a c d := by
rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, online_of_col_online ab aL bL col_124⟩ 
--2023/4/8
theorem tri_143_of_tri_col (ad : a ≠ d) (tri_abc : triangle a b c) (col_abd : colinear a b d) :
  triangle a d c := fun col_adc => by rcases col_abd with ⟨L, aL, bL, dL⟩; exact tri_abc 
                                        ⟨L, aL, bL, online_of_col_online ad aL dL col_adc⟩ 
--2023/4/8
theorem col_of_B (Babc : B a b c) : colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact ⟨L, aL, bL, online_3_of_B Babc aL bL⟩
--2023/4/13
theorem pt_inter_of_not_sameside (abL : ¬sameside a b L) : 
    ∃ c M, online a M ∧ online b M ∧ online c M ∧ online c L := by
   rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases pt_of_lines_inter $ lines_inter_of_not_sameside 
    aM bM abL with ⟨c, cL, cM⟩; refine ⟨c, M, aM, bM, cM, cL⟩
--2023/4/13
theorem ne_of_diffside (abL : diffside a b L) : a ≠ b := 
  fun ab => by rw [ab] at abL; exact abL.2.2 $ sameside_rfl_of_not_online abL.1
--2023/4/13
theorem ne_of_online (aL : online a L) (bL : ¬online b L) : a ≠ b := 
  fun ab => by rw [ab] at aL; exact bL aL
--2023/4/13
theorem ne_line_of_online (aL : online a L) (bM : online b M) (bL : ¬online b L) : L ≠ M :=
  fun LM => by rw [←LM] at bM; exact bL bM
--2023/4/13
theorem pt_B_of_diffside (abL : diffside a b L) : ∃ c, online c L ∧ B a c b := by
  rcases pt_inter_of_not_sameside abL.2.2 with ⟨c, M, aM, bM, cM, cL⟩
  refine ⟨c, cL, B_of_online_inter (Ne.symm $ ne_of_online cL abL.1) (ne_of_online cL abL.2.1) 
    (ne_of_diffside abL) (Ne.symm $ ne_line_of_online cL bM abL.2.1) aM cM bM cL abL.2.2⟩ 
--2023/4/13
theorem B_of_three_col_ne (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (col_abc : colinear a b c) :
    B a b c ∨ B b a c ∨ B a c b := by 
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact B_of_three_online_ne ab ac bc aL bL cL
--2023/4/13
theorem B_of_length_eq_col (ab : a ≠ b) (ac : a ≠ c) (col_abc : colinear a b c) 
    (ab_cb : length a b = length c b) : B a b c := by
  rcases B_of_three_col_ne ab ac (ne_of_ne_len ab $ by rwa [length_symm b c]) col_abc 
    with Babc | Bet | Bet; exact Babc; repeat {linarith [length_sum_perm_of_B Bet]}
--2023/4/13
theorem length_zero_of_eq (ab : a = b) : length a b = 0 := (length_eq_zero_iff).mpr ab
--2023/4/13
theorem eq_of_length_zero (ab_0 : length a b = 0) : a = b := (length_eq_zero_iff).mp ab_0
--2023/4/13
theorem ne_of_triangle_length_eq (tri_abc : triangle a b c) (bd_cd : length b d = length c d) :
    b ≠ d := fun bd => ne_23_of_tri tri_abc $ bd.trans (eq_of_length_zero $ bd_cd.symm.trans $ 
      length_zero_of_eq bd).symm
--2023/4/14
theorem len_21_of_len (ab_r : length a b = r) : length b a = r := by rwa [length_symm b a]
--2023/4/14
theorem len_43_of_len (ab_r : r = length a b) : r = length b a := by rwa [length_symm b a]
--2023/4/14
theorem len_2143_of_len (ab_cd : length a b = length c d) : length b a = length d c := 
  by rwa [length_symm b a, length_symm d c]
--2023/4/14
theorem ang_321_of_ang (abc_r : angle a b c = r) : angle c b a = r := by rwa [angle_symm c b a]
--2023/4/14
theorem ang_654_of_ang (abc_r : r = angle a b c) : r = angle c b a := by rwa [angle_symm c b a]
--2023/4/14
theorem ang_654321_of_ang (abc_def : angle a b c = angle d e f) : angle c b a = angle f e d := 
  by rwa [angle_symm c b a, angle_symm f e d]
--2023/4/14
theorem online_of_B_online (Babc : B a b c) (aL : online a L) (cL : ¬online c L) : ¬online b L :=
  fun bL => cL (online_3_of_B Babc aL bL)
--2023/4/14
theorem sameside_of_B_online_3 (Babc : B a b c) (aL : online a L) (cL : ¬online c L) :
    sameside b c L := sameside_of_B_not_online_2 Babc aL $ online_of_B_online Babc aL cL
--2023/4/14
theorem ne_of_sameside' (cL : online c L) (abL : sameside a b L) : c ≠ a := 
  ne_of_online cL $ not_online_of_sameside abL 
--2023/4/14
theorem tri_of_B_B_tri (Babd : B a b d) (Bace : B a c e) (tri_abc : triangle a b c) : 
    triangle a d e := tri132_of_tri123 $ tri_143_of_tri_col (ne_13_of_B Bace) (tri132_of_tri123 $ 
  tri_143_of_tri_col (ne_13_of_B Babd) tri_abc $ col_of_B Babd) $ col_of_B Bace
--2023/4/17
theorem ne_21_of_B (Babc : B a b c) : b ≠ a := Ne.symm $ ne_12_of_B Babc

theorem ne_of_B_B (Babc : B a b c) (Bbcd : B b c d) : a ≠ d := 
  ne_13_of_B $ B124_of_B123_B234 Babc Bbcd

theorem ne_of_B_B_B (Babc : B a b c) (Bbcd : B b c d) (Bcde : B c d e) : a ≠ e :=
  ne_13_of_B $ B124_of_B123_B234 Babc (B124_of_B123_B234 Bbcd Bcde)

theorem sameside_or_of_diffside' (cL : ¬online c L) (abL : diffside a b L) : 
    sameside a c L ∨ sameside b c L := sameside_or_of_diffside abL.1 abL.2.1 cL abL.2.2

theorem rightangle_of_angle_eq (Babc : B a b c) (aL : online a L) (cL : online c L) 
    (dL : ¬online d L) (dba_dbc : angle d b a = angle d b c) : 
    angle d b a = rightangle ∧ angle d b c = rightangle := by
  have ang := ang_321_of_ang $ (angle_eq_iff_rightangle aL cL dL Babc).mp $ ang_321_of_ang dba_dbc
  exact ⟨ang, dba_dbc.symm.trans ang⟩
--2023/4/17 new
theorem diffside_of_not_online' (aL : ¬online a L) : ∃ b, diffside a b L := by
  rcases diffside_of_not_online aL with ⟨b, bL, abL⟩; exact ⟨b, aL, bL, abL⟩

theorem pts_line_circle_of_not_sameside (aα : center_circle a α) (bα : on_circle b α) 
    (abL : ¬sameside a b L) : ∃ c d, c ≠ d ∧ 
    online c L ∧ online d L ∧ on_circle c α ∧ on_circle d α :=
  pts_of_line_circle_inter $ line_circle_inter_of_not_sameside abL 
  (by right; exact inside_circle_of_center aα) $ by left; exact bα
 ---------------------------------------- Book I Refactored --------------------------------------------
              /-- Euclid I.1, construction of two equilateral triangles -/
theorem iseqtri_iseqtri_diffside_of_ne (ab : a ≠ b) : ∃ (c d : point), ∃ (L : line), online a L ∧
  online b L ∧ diffside c d L ∧ eq_tri a b c ∧ eq_tri a b d := by
rcases circle_of_ne ab with ⟨α, aα, bα⟩
rcases circle_of_ne (Ne.symm ab) with ⟨β, bβ, aβ⟩
rcases diffside_of_circles_inter aα bβ (circles_inter_of_inside_on_circle bα aβ
  (inside_circle_of_center aα) (inside_circle_of_center bβ)) with 
  ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩
have ab_ac := (on_circle_iff_length_eq aα bα).mpr cα
have bc_ba := (on_circle_iff_length_eq bβ cβ).mpr aβ
have ab_ad := (on_circle_iff_length_eq aα bα).mpr dα
have bd_ba := (on_circle_iff_length_eq bβ dβ).mpr aβ
exact ⟨c, d, L, aL, bL, cdL, eq_tri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
  eq_tri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩
--2023/4/17
/-- Euclid I.1, construction of an equilateral triangle on the sameside of a point -/
theorem iseqtri_sameside_of_ne (ab : a ≠ b) (aL : online a L) (bL : online b L) (dL : ¬online d L) 
    : ∃ c, ¬online c L ∧ sameside c d L ∧ eq_tri a b c := by
  rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c1, c2, M, aM, bM, c1c2M, eqtri1, eqtri2⟩
  rcases sameside_or_of_diffside' dL (by rwa [line_unique_of_pts ab aM bM aL bL] at c1c2M) 
    with c1dL | c2dL
  refine ⟨c1, not_online_of_sameside c1dL, c1dL, eqtri1⟩
  refine ⟨c2, not_online_of_sameside c2dL, c2dL, eqtri2⟩

              /-- Euclid I.1, construction of a single equilateral triangle -/
theorem iseqtri_of_ne (ab : a ≠ b) : ∃ (c : point), eq_tri a b c :=
  by rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c, -, -, -, -, -, eqtri, -⟩; exact ⟨c, eqtri⟩
                          /-- Euclid I.2, collapsing compass -/
theorem length_eq_of_ne (a : point) (bc : b ≠ c) : ∃ (f : point), length a f = length b c := by
  by_cases ab : a = b; rw [ab]; exact ⟨c, rfl⟩ --degenerate case
  rcases iseqtri_of_ne ab with ⟨d, eqtri⟩
  rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩
  rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩
  have be_bc := (length_eq_of_oncircle bα cα eα).symm
  have de_df := length_eq_of_oncircle dβ eβ fβ
  have af_be := length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 de_df
  exact ⟨f, af_be.trans be_bc⟩ --calc block?
                          /-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne (ab : a ≠ b) (bc : b ≠ c) :
  ∃ (d : point), B a b d ∧ length b c = length b d := by 
rcases B_circ_of_ne ab bc with ⟨d, α, Babd, bα, cα, dα⟩;
  exact ⟨d, Babd, length_eq_of_oncircle bα cα dα⟩
                          /-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne_four (ab : a ≠ b) (cd : c ≠ d) :
  ∃ (f : point), B a b f ∧ length c d = length b f := by
rcases length_eq_of_ne b cd with ⟨e, be_cd⟩
rcases length_eq_B_of_ne ab (ne_of_ne_len' cd be_cd) with ⟨f, Babf, be_bf⟩
exact ⟨f, Babf, by linarith⟩
                /-- Euclid I.3, Moving a smaller segment on top of a larger one -/
theorem B_length_eq_of_ne_lt (cd : c ≠ d) (cd_lt_ab : length c d < length a b) :
  ∃ (f : point), B a f b ∧ length a f = length c d := by
rcases length_eq_of_ne a cd with ⟨e, ae_cd⟩
rcases circle_of_ne (ne_of_ne_len' cd ae_cd) with ⟨α, aα, eα⟩ --combine into one line?
rcases B_oncircle_of_inside_outside (inside_circle_of_center aα) 
  (out_circle_of_lt aα eα (by rwa [← ae_cd] at cd_lt_ab)) with ⟨f, Bafb, fα⟩
have ae_af := length_eq_of_oncircle aα eα fα
exact ⟨f, Bafb, by linarith⟩
                      /-- Euclid I.5, (part 1), isosceles triangles have equal angles -/
theorem angle_eq_of_iso (iso_abc : iso_tri a b c) : angle a b c = angle a c b :=
  (sas (iso_abc).2 (iso_abc).2.symm (angle_symm b a c)).2.2.symm
                      /-- Euclid I.6, a triangle with equal angles is isosceles -/
theorem iso_of_angle_eq (tri_abc : triangle a b c) (abc_eq_acb : angle a b c = angle a c b) :
  length a b = length a c := by
by_contra ab_ac
wlog ab_le_ac : length a b ≤ length a c; exact this (tri132_of_tri123 tri_abc) abc_eq_acb.symm 
  (Ne.symm ab_ac) $ by linarith
rcases B_length_eq_of_ne_lt (ne_12_of_tri tri_abc) 
  (by rw [length_symm c a] at *; exact Ne.lt_of_le ab_ac ab_le_ac) with ⟨d, Bcda, cd_ab⟩
have ar_cdb_eq_bac := area_eq_of_sas (by rwa [length_symm b a]) (length_symm c b) $
  (angle_extension_of_B (ne_32_of_tri tri_abc) Bcda).trans abc_eq_acb.symm
have split_ar_bca := area_add_of_B Bcda (tri231_of_tri123 tri_abc)
have ar_abd_zero : area a b d = 0 := by 
  linarith [area_invariant b d a, area_invariant b a c, area_invariant c d b]
have col_abd := col_132_of_col $ col_of_area_zero_ne (ne_12_of_tri tri_abc) ar_abd_zero
exact tri_abc $ col_134_of_col_123_col_124 (Ne.symm $ ne_23_of_B Bcda) 
  col_abd (col_of_B $ B_symm Bcda)
  
/-- Euclid I.10, bisecting a segment -/
theorem bisect_segment (ab : a ≠ b) : ∃ (e : point), B a e b ∧ length a e = length b e := by
  rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c, d, L, aL, bL, cdL, eqtri_abc, eqtri_abd⟩
  rcases pt_B_of_diffside cdL with ⟨e, eL, Bced⟩
  have acd_bcd : angle a c d = angle b c d := (sss (len_2143_of_len eqtri_abc.2.2.2) rfl $ 
    len_2143_of_len eqtri_abd.2.2.2).1
  have ae_be : length a e = length b e := (sas eqtri_abc.2.2.2 rfl $ by 
    linarith [ang_654321_of_ang $ angle_extension_of_B (Ne.symm $ ne_13_of_tri eqtri_abc.1) Bced,
    ang_654321_of_ang $ angle_extension_of_B (Ne.symm $ ne_23_of_tri eqtri_abc.1) Bced]).1
  refine ⟨e, B_of_length_eq_col (ne_of_triangle_length_eq 
    (tri312 eqtri_abc.1) ae_be) ab ⟨L, aL, eL, bL⟩ ae_be, ae_be⟩

/-- Euclid I.9 lemma, bisecting an angle in an isosceles triangle -/
theorem bisect_angle_iso (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M) 
    (iso_abc : iso_tri a b c) : ∃ (d : point), angle b a d = angle c a d ∧ sameside d b M ∧ 
    sameside d c L := by
  rcases bisect_segment (ne_23_of_tri iso_abc.1) with ⟨d, Bbdc, bd_cd⟩
  have bad_cad : angle b a d = angle c a d := (sss bd_cd rfl $ len_2143_of_len iso_abc.2).2.2
  refine ⟨d, bad_cad, sameside_of_B_online_3 (B_symm Bbdc) cM $ online_2_of_triangle aM cM 
    iso_abc.1, sameside_of_B_online_3 Bbdc bL $ online_3_of_triangle aL bL iso_abc.1⟩

/-- Euclid I.9 lemma, bisecting an angle -/
theorem bisect_angle (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M) 
    (tri_abc : triangle a b c) : ∃ (f : point), angle b a f = angle c a f ∧ sameside f b M ∧ 
    sameside f c L := by
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_abc) (ne_13_of_tri tri_abc) with ⟨d, Babd, ac_bd⟩
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_12_of_tri tri_abc) with ⟨e, Bace, ab_ce⟩
  rcases bisect_angle_iso aL (online_3_of_B Babd aL bL) aM (online_3_of_B Bace aM cM) 
    ⟨tri_of_B_B_tri Babd Bace tri_abc, by linarith[length_sum_of_B Babd, length_sum_of_B Bace]⟩ 
    with ⟨f, daf_eaf, fdM, feL⟩
  refine ⟨f, by linarith[angle_extension_of_B (ne_of_sameside' aL feL) Babd, 
    angle_extension_of_B (ne_of_sameside' aL feL) Bace], sameside_trans (sameside_symm fdM) $ 
    sameside_symm $ sameside_of_B_not_online_2 Babd aM (online_2_of_triangle aM cM tri_abc), 
    sameside_trans (sameside_symm feL) $ sameside_symm $ sameside_of_B_not_online_2 Bace aL 
    (online_3_of_triangle aL bL tri_abc)⟩

lemma B_B_eq_of_B (Babc : B a b c) : ∃ d e, B b c d ∧ B b a e ∧ length b d = length b e := by
  rcases length_eq_B_of_ne_four (ne_23_of_B Babc) (ne_12_of_B Babc) with ⟨d, Bbcd, ab_cd⟩
  rcases length_eq_B_of_ne_four (ne_21_of_B Babc) (ne_23_of_B Babc) with ⟨e, Bbae, bc_ae⟩
  refine ⟨d, e, Bbcd, Bbae, by linarith[length_sum_of_B Bbcd, length_sum_perm_of_B Bbae]⟩

lemma B_B_eq_of_B_I11 (Babc : B a b c) (aL : online a L) (cL : online c L) : 
    ∃ d e, e ≠ d ∧ B b c d ∧ B b a e ∧ online b L ∧ online e L ∧ online d L 
    ∧ length b d = length b e := by
  rcases B_B_eq_of_B Babc with ⟨d, e, Bbcd, Bbae, bd_be⟩
  have bL := online_2_of_B Babc aL cL
  exact ⟨d, e, ne_of_B_B_B (B_symm Bbae) Babc Bbcd, Bbcd, Bbae, bL, 
    online_3_of_B Bbae bL aL, online_3_of_B Bbcd bL cL, bd_be⟩
  
/-- Euclid I.11, Obtaining perpendicular angles from a point on a line -/
theorem perpendicular_of_online (Babc : B a b c) (aL : online a L) (cL : online c L) 
    (gL : ¬online g L) : 
    ∃ f, sameside f g L ∧ angle f b a = rightangle ∧ angle f b c = rightangle := by
  rcases B_B_eq_of_B_I11 Babc aL cL with ⟨d, e, ed, Bbcd, Bbae, bL, eL, dL, bd_be⟩
  rcases iseqtri_sameside_of_ne ed eL dL gL with ⟨f, fL, fgL, eqtri⟩
  have fbe_fbd : angle f b e = angle f b d := (sss rfl eqtri.2.2.2 bd_be.symm).2.1
  have rightangles : angle f b a = rightangle ∧ angle f b c = rightangle := 
    rightangle_of_angle_eq Babc aL cL fL $ by linarith
      [ang_654321_of_ang $ angle_extension_of_B (ne_of_online bL fL) Bbcd, 
       ang_654321_of_ang $ angle_extension_of_B (ne_of_online bL fL) Bbae]
  refine ⟨f, fgL, rightangles⟩ 

/-- Euclid I.12, Obtaining perpendicular angles from a point off a line -/
theorem perpendicular_of_not_online (aL : ¬online a L) : ∃ c d e, B c e d ∧ online c L ∧ online d L 
    ∧ online e L ∧ angle a e c = rightangle ∧ angle a e d = rightangle := by
  rcases diffside_of_not_online' aL with ⟨b, abL⟩
  rcases circle_of_ne (ne_of_diffside abL) with ⟨α, aα, bα⟩
  rcases pts_line_circle_of_not_sameside aα bα abL.2.2 with ⟨c, d, cd, cL, dL, cα, dα⟩
  rcases bisect_segment cd with ⟨e, Bced, ce_de⟩
  have aec_aed : angle a e c = angle a e d := (sss (length_eq_of_oncircle aα cα dα) ce_de rfl).2.2
  have rightangles : angle a e c = rightangle ∧ angle a e d = rightangle := 
    rightangle_of_angle_eq Bced cL dL aL aec_aed
  refine ⟨c, d, e, Bced, cL, dL, online_2_of_B Bced cL dL, rightangles⟩
    -------------------------------------------- Book I Old--------------------------------------------
--Euclid I.13
theorem flatsumright {a b c d : point} {L : line} (dL : online d L) (cL : online c L)
  (aL : ¬online a L) (Bdbc : B d b c) : angle a b c + angle a b d = 2 * rightangle :=
  by sorry /-begin
  --have := bet_nq2 dL cL aL Bdbc,
  have ab : a≠ b:= (neq_of_bet dL cL aL Bdbc).symm,
  rcases line_of_pts a b with ⟨N, aN, bN⟩,
  by_cases (angle a b c = angle a b d),
  { linarith [(angle_eq_iff_rightangle dL cL aL Bdbc).mp ((angle_symm_of_angle h.symm)), (angle_symm_of_angle  h.symm)], },
  rcases perplinecor cL dL aL (B_symm Bdbc) with ⟨e, a1, a2, eaL⟩,
  have eb := (neq_of_online_offline (online_2_of_B Bdbc dL cL) (not_online_of_sameside eaL)).symm,
  rcases line_of_pts e b with ⟨M, eM, bM⟩,
  have ra : angle e b c = angle e b d := by linarith [angle_symm c b e, angle_symm d b e],
  have aM : ¬online a M,
  { intro aM,
    have ae : a ≠ e := λ ae, (by rwa ae at h : (¬(angle e b c = angle e b d))) ra,
    cases B_of_three_online_ne (neq_of_online_offline (online_2_of_B Bdbc dL cL) aL).symm ae eb.symm aM bM eM ,
    --- *** BAD don't use `h_1`
    { exact (not_sameside13_of_B123_online2 h_1 (online_2_of_B Bdbc dL cL)) (sameside_symm eaL), },
    cases h_1,
    exact (by rwa [angle_extension_of_B (ne_23_of_B Bdbc) h_1,
      angle_extension_of_B ((ne_12_of_B Bdbc).symm) h_1] at h : (¬(angle e b c = angle e b d))) ra,
    exact (by rwa [←(angle_extension_of_B (ne_23_of_B Bdbc) (B_symm h_1)),
      ←(angle_extension_of_B ((ne_12_of_B Bdbc).symm) (B_symm h_1))] at h : (¬(angle e b c = angle e b d))) ra, },
  -- wlog acM : (sameside a c M) using [c d, d c],
  -- { by_cases h1 : sameside a c M,
  --   { left, assumption, },
  --   right,
  --   have cM : ¬online c M := λ cM, (not_online_of_sameside eaL)
  --     (by rwa (line_unique_of_pts (ne_23_of_B Bdbc) bM cM (online_2_of_B Bdbc dL cL) cL) at eM),
  --   have dM : ¬online d M := λ dM, (not_online_of_sameside eaL)
  --     (by rwa (line_unique_of_pts ((ne_12_of_B Bdbc).symm) bM dM (online_2_of_B Bdbc dL cL) dL) at eM),
  --   exact sameside_of_diffside_diffside ⟨cM, aM, difsym h1⟩ ⟨cM, dM, difsym (not_sameside13_of_B123_online2 Bdbc bM)⟩, },
  --   --end of proof of wlog; not worth it?
  -- { have splitcbe := (angle_add_iff_sameside (ne_23_of_B Bdbc) eb.symm (online_2_of_B Bdbc dL cL) cL bM eM  aM aL (λ LM, (not_online_of_sameside eaL)
  --     (by rwa ← LM at eM))).mpr ⟨sameside_symm acM, eaL⟩,
  --   have eNL : ¬online e N ∧ ¬online e L := ⟨(λ eN, (by rwa (line_unique_of_pts eb eM bM eN bN) at aM :
  --     ¬online a N) aN), (λ eL, (not_online_of_sameside eaL) eL)⟩,
  --   have deN : sameside d e N,
  --   { have cN : ¬online c N := λ cN,
  --       aL (by rwa (line_unique_of_pts (ne_23_of_B Bdbc) bN cN (online_2_of_B Bdbc dL cL) cL) at aN),
  --     have dN : ¬online d N  := λ dN,
  --       aL (by rwa (line_unique_of_pts ((ne_12_of_B Bdbc).symm) bN dN (online_2_of_B Bdbc dL cL) dL) at aN),
  --     exact sameside_symm (sameside_of_diffside_diffside ⟨cN, eNL.1, difsym (not_sameside_of_sameside_sameside bM bN (online_2_of_B Bdbc dL cL) eM aN cL acM eaL)⟩
  --       ⟨cN, dN, difsym (not_sameside13_of_B123_online2 Bdbc bN)⟩), },
  --   have splitabd := (angle_add_iff_sameside ab.symm ((ne_12_of_B Bdbc).symm) bN aN (online_2_of_B Bdbc dL cL) dL  eNL.2 eNL.1
  --     (λ NL, aL (by rwa NL at aN))).mpr ⟨sameside_symm eaL, deN⟩,
  --   have flipcbe := angle_symm c b e,
  --   have flipabc := angle_symm a b c,
  --   linarith [(angle_eq_iff_rightangle dL cL eNL.2 Bdbc).mp (by linarith)], },
  -- linarith [this cL dL (B_symm Bdbc) (λ hh, h hh.symm) a2 a1 ra.symm],
  by sorry,
end-/

-- Euclid I.14
theorem rightimpflat {a b c d : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cdN : diffside c d N) (ang : angle a b c + angle a b d = 2 * rightangle) : B c b d :=
  by sorry /-begin
  have cd := difneq cdN, --API and degenerate cases
  have bd : b ≠ d := λ bd, cdN.2.1 (by rwa bd at bN),
  rcases same_length_B_of_ne (neq_of_online_offline bN cdN.1).symm (neq_of_online_offline bN cdN.1) with ⟨e, Bcbe, len⟩,
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  have eM := online_3_of_B Bcbe cM bM,
  have eN : ¬online e N := λ eN, cdN.1 (online_3_of_B (B_symm Bcbe) eN bN),
  have edN := sameside_of_diffside_diffside ⟨cdN.1, eN, difsym (not_sameside13_of_B123_online2 (B_symm Bcbe) bN)⟩ cdN,
  rcases line_of_pts b d with ⟨L, bL, dL⟩,
  have LN : L ≠ N := λ LN, cdN.2.1 (by rwa LN at dL),
  by_cases eL : online e L,
  { exact B_of_online_inter  (neq_of_online_offline bN cdN.1).symm bd cd LN (online_3_of_B (B_symm Bcbe) eL bL) bL dL bN  cdN.2.2, },
  have dM : ¬online d M := λ dM, eL (by rwa (line_unique_of_pts bd bM dM bL dL) at eM),
  have ae : a ≠ e := λ ae, eN (by rwa ae at aN),
  by_cases ed : e = d, { rwa ed at Bcbe, },
  have ang1 := flatsumright cM eM (λ aM, cdN.1 (by rwa ← (line_unique_of_pts ab aN bN aM bM) at cM)) Bcbe, --  beginning of proof
  -- by_cases eaL : sameside e a L,
  -- { have split := (angle_add_iff_sameside bd ab.symm bL dL bN aN eN eL LN).mpr ⟨sameside_symm edN, sameside_symm eaL⟩,
  --   have dM := ((angle_zero_iff_online (ne_23_of_B Bcbe) bd bM eM).mpr (by linarith [angle_symm a b e,
  --     angle_symm a b d, angle_symm d b e])).1,
  --   exact B_of_online_inter  (by show_term{btw}) bd cd ((λ NM, eN (by rwa NM at eM)) : M≠ N) cM bM dM bN  cdN.2.2 },
  -- have adM := sameside_of_sameside_not_sameside ab.symm bN bL bM aN dL eM eL (sameside_symm edN) (difsym eaL),
  -- have split := (angle_add_iff_sameside ab.symm (ne_23_of_B Bcbe) bN aN bM eM dM (not_online_of_sameside (sameside_symm edN))
  --   (λ NM, eN (by rwa ← NM at eM))).mpr ⟨adM, edN⟩,
  -- have dM := ((angle_zero_iff_online (ne_23_of_B Bcbe) bd bM eM).mpr (by linarith [angle_symm a b e,
  --   angle_symm a b d, angle_symm d b e])).1,
  -- exact B_of_online_inter (by show_term{btw}) bd cd (((λ NM, eN (by rwa NM at eM)) : M≠ N)) cM bM dM bN  cdN.2.2,
  by sorry,
end-/

--Euclid I.15
theorem vertang {a b c d e : point} {L : line} (cL : online c L) (dL : online d L)
  (aL : ¬online a L) (Bced : B c e d) (Baeb : B a e b) : angle b e c = angle d e a :=
  by sorry /-begin
  rcases line_of_B Baeb with ⟨N, aN, eN, bN, -,nq,-⟩,
  have dN : ¬online d N := λ dN,
    ((by rwa (line_unique_of_pts (ne_23_of_B Bced) (online_2_of_B Bced cL dL) dL eN dN) at aL) : ¬online a N) aN,
  have bL : ¬online b L := λ bL,
    (by rwa line_unique_of_pts nq (online_2_of_B Bced cL dL) bL eN bN at aL : ¬online a N) aN,
  have := flatsumright cL dL bL Bced,
  have := flatsumright aN bN dN Baeb,
  linarith [angle_symm a e d, angle_symm b e d],
end-/

--Euclid I.16 (Elliptic geometry fails)
theorem extang {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L) (dL : online d L)
  (Bbcd : B b c d) : angle b a c < angle a c d :=
  by sorry /-begin
  have cL := online_2_of_B Bbcd bL dL,
  have ca := neq_of_online_offline cL aL,
  have ba := neq_of_online_offline bL aL,
  rcases bisline ca with ⟨e, Bcea, len⟩,
  have be : b ≠ e := λ be, aL (online_3_of_B Bcea cL (by rwa be at bL)),
  rcases same_length_B_of_ne be be.symm with ⟨f, Bbef, len2⟩,
  have cf : c ≠ f := λ cf, aL (online_3_of_B Bcea cL (online_2_of_B Bbef bL (by rwa cf at cL))),
  have afL := sameside_trans (sameside_of_B_not_online_2 Bcea cL (λ eL, aL ((online_3_of_B Bcea) cL eL)))
    (sameside_of_B_not_online_2 Bbef bL (λ eL, aL ((online_3_of_B Bcea) cL eL))),
  rcases line_of_B Bbef with ⟨M, bM, eM, fM, -⟩,
  have cM : ¬online c M := λ cM,
    ((by rwa ← (line_unique_of_pts (ne_12_of_B Bbcd) bM cM bL cL) at aL) : ¬online a M) (online_3_of_B Bcea cM eM),
  have ang := vertang bM fM cM Bbef Bcea,
  have ang2 := (sas (len_symm_of_len len2.symm).symm (len_symm_of_len len) (by linarith [angle_symm b e a])).2.2,
  rcases line_of_B Bcea with ⟨N, cN, eN, aN, -,-,nq⟩,
  have fN : ¬online f N := λ fN,
    aL (by rwa (line_unique_of_pts (ne_12_of_B Bbcd) (online_3_of_B (B_symm Bbef) fN eN) cN bL cL) at aN),
  have bN : ¬online b N := λ bN, fN (online_3_of_B Bbef bN eN),
  have dfN := sameside_symm (sameside_of_diffside_diffside ⟨bN, fN, not_sameside13_of_B123_online2 Bbef eN⟩ ⟨bN, (λ dN, bN (online_3_of_B (B_symm Bbcd) dN cN)),
    not_sameside13_of_B123_online2 Bbcd cN⟩),
  have NL : N ≠ L := λ NL, bN (by rwa ←NL at bL), --start of pf below, API above
  have splitang := (angle_add_iff_sameside nq.symm (ne_23_of_B Bbcd) cN aN cL dL (not_online_of_sameside (sameside_symm afL))
    (not_online_of_sameside (sameside_symm dfN)) NL).mpr ⟨afL, dfN⟩,
  rcases line_of_pts c f with ⟨P, cP, fP⟩,
  have geq := lt_of_le_of_ne (angle_nonneg f c d) (ne_comm.mp (mt (angle_zero_iff_online cf (ne_23_of_B Bbcd) cP fP).mpr _)),--better way to deal with or?
  have geq2 := lt_of_le_of_ne (angle_nonneg b a c) (angeasy ca ((ne_12_of_B Bbcd).symm)
    (ne_comm.mp (mt (angle_zero_iff_online ca.symm ba.symm aN cN).mpr _))),
  linarith [angle_symm c a b, angle_extension_of_B ba.symm (B_symm Bcea), angle_extension_of_B cf Bcea],
  exact λ bN, NL (line_unique_of_pts (ne_12_of_B Bbcd) bN.1 cN bL cL),
  exact λ dP, not_online_of_sameside (sameside_symm (by rwa ←(line_unique_of_pts (ne_23_of_B Bbcd) cP dP.1 cL dL) at afL)) fP,
end-/

--Euclid I.16 (Elliptic geometry fails)
theorem extangcor {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L)
  (dL : online d L) (Bbcd : B b c d) : angle a b c < angle a c d :=
  by sorry /-begin
  rcases same_length_B_of_ne (neq_of_online_offline (online_2_of_B Bbcd bL dL) aL).symm (neq_of_online_offline (online_2_of_B Bbcd bL dL) aL) with ⟨g, Bacg, len3⟩,
  have gb : g ≠ b := λ gb, aL (online_3_of_B (B_symm Bacg) (by rwa ← gb at bL) (online_2_of_B Bbcd bL dL)),
  have := angle_symm2_of_angle (ne_23_of_B Bacg).symm gb (ne_23_of_B Bbcd).symm (neq_of_online_offline dL aL)
    (vertang bL dL aL Bbcd Bacg),
  rcases line_of_B Bacg with ⟨N, aN, cN, gN, nq⟩,
  linarith [extang (λ bN, aL (by rwa line_unique_of_pts (ne_12_of_B Bbcd) bN cN bL (online_2_of_B Bbcd bL dL) at aN)) aN gN Bacg],
end-/

 --Euclid I.18
 theorem sidebigang {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (length : length a b < length a c) : angle b c a < angle a b c :=
  by sorry /-begin
  rcases same_length_B_of_ne_le (neq_of_online_offline bL aL).symm length with ⟨d, Badc, len2⟩,
  rcases line_of_B Badc with ⟨M, aM, dM, cM, nq0,nq1,nq2⟩,
  have ang := extangcor (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)) cM aM (B_symm Badc),
  have db : d ≠ b := neq_of_online_offline dM (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)),
  have LM : L ≠ M := λ LM, aL (by rwa LM.symm at aM),
  rcases line_of_pts b a with ⟨N, bN, aN⟩,
  have adL : sameside a d L, {by_contra adL, exact not_B_symm (not_B_of_B (B_symm Badc))
    (B_of_online_inter nq2.symm nq1.symm (ne_12_of_B Badc) LM.symm aM cM dM cL  adL), },
  rcases line_of_pts d b with ⟨P, dP, bP⟩,
  have aP : ¬online a P := λ aP, LM (line_unique_of_pts bc bL cL (by rwa (line_unique_of_pts nq0 aP dP aM dM) at bP) cM),
  have cdN := sameside_of_sameside_not_sameside bc bL bP bN cL dP aN aP (sameside_symm adL) (not_sameside13_of_B123_online2 (B_symm Badc) dP),
  have splitang := (angle_add_iff_sameside bc (neq_of_online_offline bL aL) bL cL bN aN (not_online_of_sameside (sameside_symm cdN)) (not_online_of_sameside (sameside_symm adL))
    (λ LN, aL (by rwa ← LN at aN))).mpr ⟨cdN, adL⟩,
  have := eq_angle_of_eq_length (ne_12_of_B Badc) db len2,
  linarith [angle_symm c b a, angle_symm d b a, angle_symm a d b, (angle_nonneg c b d),
    angle_extension_of_B bc.symm (B_symm Badc), angle_symm b c d, angle_symm b c a],
end-/

--Euclid I.19 -- Probably can be turned into one line
theorem angbigside {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (ang : angle b c a < angle a b c) : length a b < length a c :=
  by sorry /-begin
  by_cases len : length a b = length a c,
  { linarith [angle_symm b c a, eq_angle_of_eq_length (neq_of_online_offline bL aL).symm bc len], },
  by_cases len2 : length a c < length a b,
  { linarith [sidebigang bc.symm cL bL aL len2, angle_symm c b a, angle_symm b c a], },
  push_neg at len2,
  exact (ne.le_iff_lt len).mp len2,
end-/

--Euclid I.20
theorem triineq {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : length b c < length a b + length a c :=
  by sorry /-begin
  have bc := neq_of_online_offline bL cL,
  rcases same_length_B_of_ne ab.symm (neq_of_online_offline aL cL) with ⟨d, Bbad, len⟩,
  have dc := neq_of_online_offline (online_3_of_B Bbad bL aL) cL,
  have ang := eq_angle_of_eq_length (ne_23_of_B Bbad) dc (len_symm_of_len len.symm).symm,
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  rcases line_of_pts d c with ⟨N, dN, cN⟩,
  have aN : ¬online a N := λ aN,
    cL (by rwa ← (line_unique_of_pts (ne_23_of_B Bbad) aL (online_3_of_B Bbad bL aL) aN dN) at cN),
  have adM := sameside_of_B_not_online_2 Bbad bM (λ aM, cL (by rwa (line_unique_of_pts ab aM bM aL bL) at cM)),
  have abN := sameside_of_B_not_online_2 (B_symm Bbad) dN aN,
  have angsplit := angles_add_of_sameside dc.symm bc.symm cN dN cM bM (sameside_symm adM) (sameside_symm (sameside_of_B_not_online_2 (B_symm Bbad) dN aN)),
  have bigside := angbigside dc.symm cN dN (not_online_of_sameside (sameside_symm abN)) (by linarith [angle_extension_of_B dc (B_symm Bbad),
    angle_symm d c b, angle_symm d c a, angle_symm c d b]),
  linarith [length_symm b a, length_symm c a, length_sum_of_B Bbad],
end-/

--Euclid I.20
theorem triineqcor {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : length b c < length a b + length a c ∧ length a c < length a b + length b c ∧
  length a b < length a c + length b c :=
  by sorry /-begin
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  rcases line_of_pts a c with ⟨N, aN, cN⟩,
  have aM : ¬online a M := λ aM, cL (by rwa ← (line_unique_of_pts ab aL bL aM bM) at cM),
  have bN : ¬online b N := λ bN, cL (by rwa (line_unique_of_pts ab aN bN aL bL) at cN),
  exact ⟨triineq ab aL bL cL, by linarith [length_symm a b, length_symm a c, triineq (neq_of_online_offline bL cL) bM cM aM],
    by linarith [length_symm a c, length_symm b c, triineq (neq_of_online_offline aL cL).symm cN aN bN]⟩,
end-/

--Euclid I.22
theorem trimake {a1 a2 b1 b2 c1 c2 d f g : point} {L : line} (dL : online d L) (fL : online f L)
  (gL : ¬online g L) (ab : length c1 c2 < length a1 a2 + length b1 b2)
  (bc : length a1 a2 < length b1 b2 + length c1 c2) (ac : length b1 b2  < length a1 a2 + length c1 c2)
  (len : length d f = length a1 a2) :
  ∃ (k : point), length d k = length b1 b2 ∧ length f k = length c1 c2 ∧ sameside g k L :=
  by sorry /-begin
  have df : d ≠ f := nq_of_len_pos (by linarith),
  have b1b2 : b1 ≠ b2,
  { intro b1b2, rw b1b2 at ab; rw b1b2 at bc, linarith [length_eq_zero_iff.mpr (rfl : b2 = b2)], },--????
  have c1c2 : c1 ≠ c2,
  { intro c1c2, rw c1c2 at ac; rw c1c2 at bc, linarith [length_eq_zero_iff.mpr (rfl : c2 = c2)], },
  rcases same_length_B_of_ne_four df.symm b1b2 with ⟨k1, Bfdk1, lenb⟩,
  rcases same_length_B_of_ne_four df c1c2 with ⟨k2, Bdfk2, lenc⟩,
  rcases circle_of_ne (ne_23_of_B Bdfk2) with ⟨α, k2circ, fcen⟩,
  rcases circle_of_ne (ne_23_of_B Bfdk1) with ⟨β, k1circ, dcen⟩,
  rcases pt_sameside_of_circles_inter fL dL gL fcen dcen (circint_of_lt_lt fcen dcen k2circ k1circ _ (by linarith [length_symm d f])) with
    ⟨k, kgL,kalph, kbet⟩,
  refine ⟨k, by linarith [(on_circle_iff_length_eq k1circ dcen).mpr kbet], by linarith [(on_circle_iff_length_eq k2circ fcen).mpr kalph],
    sameside_symm kgL⟩,
  apply abs_lt.mpr,
  exact ⟨by linarith [length_symm f d], by linarith [length_symm f d]⟩,
  exact ordered_add_comm_monoid.to_covariant_class_left ℝ,
  exact covariant_swap_add_le_of_covariant_add_le ℝ, --why do we have to do this?
end-/

--Euclid I.23
theorem angcopy {a b c d e h : point} {L M : line} (ab : a ≠ b) (ce : c ≠ e) (cL : online c L)
  (eL : online e L) (dL : ¬online d L) (aM : online a M) (bM : online b M) (hM : ¬online h M) :
  ∃ (f : point), angle b a f = angle e c d ∧ sameside f h M :=
  by sorry /-begin
  rcases same_length_B_of_ne_four ce ab with ⟨e1, Bcee1, len⟩,
  rcases same_length_B_of_ne_four ab ce with ⟨b1, Babb1, len2⟩,
  have ineqs := triineqcor (ne_13_of_B Bcee1) cL (online_3_of_B Bcee1 cL eL) dL,
  have l3 : length a b1 = length c e1 := by linarith [length_sum_of_B Bcee1, length_sum_of_B Babb1],
  rcases trimake aM (online_3_of_B Babb1 aM bM) hM ineqs.1 ineqs.2.2 ineqs.2.1 l3 with ⟨f, l1, l2, hfM⟩,
  refine ⟨f, by linarith [(sss l3 l2 l1).2.1, angle_extension_of_B (neq_of_online_offline cL dL) Bcee1,
    angle_extension_of_B (neq_of_online_offline aM (not_online_of_sameside (sameside_symm hfM))) Babb1], sameside_symm hfM⟩,
end-/

--Euclid I.26 part 1
theorem asa {a b c d e f : point} {L : line} (ef : e ≠ f) (eL : online e L) (fL : online f L)
  (dL : ¬online d L) (side : length b c = length e f) (ang1 : angle c b a = angle f e d)
  (ang2 : angle a c b = angle d f e) :
  length a b = length d e ∧ length a c = length d f ∧ angle b a c = angle e d f :=
  by sorry /-begin
  have bc : b ≠ c := λ bc, by linarith [len_pos_of_nq ef, length_eq_zero_iff.mpr bc],
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  by_cases len : length a b = length d e,
  { have congr := sas side (len_symm2_of_len len) ang1,
    exact ⟨len, len_symm2_of_len congr.1, congr.2.2⟩, },
  by_cases len1 : length d e < length a b,
  { exfalso,
    rcases same_length_B_of_ne_le (neq_of_online_offline eL dL).symm (by linarith [length_symm a b] : length d e < length b a) with
      ⟨g, Bbga, len2⟩,
    have ac : a ≠ c, --why was this so hard to do?
    { intro ac,
      have := mt (angle_zero_iff_online bc (ne_13_of_B Bbga) bM cM).mp (by linarith [angle_pos_of_not_colinear ef eL fL dL]),
      push_neg at this,
      by_cases online a M,
      exact (ne_13_of_B (this h)).symm ac,
      exact (neq_of_online_offline cM h).symm ac, },
    have aext := angle_extension_of_B bc Bbga,
    have := angle_symm c b a,
    have gc : g ≠ c,--can be oneliner
    { intro gc,
      rw gc at *,
      linarith [len_pos_of_nq (neq_of_online_offline fL dL), length_eq_zero_iff.mpr (rfl : c = c), (sas side (len_symm_of_len len2.symm).symm
        (by linarith)).1], },
    have := angle_symm c b g,
    have sasc := sas side (len_symm_of_len len2.symm).symm (by linarith),
    rcases line_of_pts a c with ⟨N, aN, cN⟩,
    have gM : ¬online g M,--oneliner?
    { intro gM,
      have := (area_zero_iff_online bc bM cM).mpr gM,
      exact (mt (area_zero_iff_online ef eL fL).mp dL) (by rwa (area_eq_of_SSS side sasc.1 (len_symm_of_len len2)) at this), },
    rcases line_of_B Bbga with ⟨O, bO, gO, aO, -,nq,-⟩,
    have gN : ¬online g N := λ gN, (lines_neq_of_online_offline gN gM) (line_unique_of_pts bc (by rwa (line_unique_of_pts nq gO aO gN aN) at
      bO : online b N) cN bM cM),
    have key := angles_add_of_sameside ac.symm bc.symm cN aN cM bM (sameside_symm (sameside_of_B_not_online_2 Bbga bM gM))
      (sameside_symm (sameside_of_B_not_online_2 (B_symm Bbga) aN gN)),
    linarith [angle_symm e f d, angle_symm g c b], },
  have ab : a ≠ b,--oneliner?
  { intro ab,
    rw ← ab at *,
    linarith [angle_symm e f d, angle_pos_of_not_colinear ef.symm fL eL dL, (angle_zero_iff_online bc.symm bc.symm cM bM).mp
      ⟨bM, (λ Bcac, (ne_13_of_B Bcac) rfl)⟩], },
  push_neg at len1,
  rcases same_length_B_of_ne_le ab (by linarith [((ne.le_iff_lt len).mp len1), length_symm d e] : length a b < length e d) with
    ⟨g, Begd, len2⟩,
  have := angle_extension_of_B ef Begd,
  have := angle_symm f e d,
  rcases line_of_pts e d with ⟨M, eM, dM⟩,
  rcases line_of_pts f d with ⟨N, fN, dN⟩,
  have gL : ¬online g L := λ gL, dL (online_3_of_B Begd eL gL),
  have sasc := sas side (len_symm_of_len len2.symm) (by linarith [angle_symm f e g]),
  have gN : ¬online g N,--oneliner?
  { intro gN,
    have := line_unique_of_pts (ne_23_of_B Begd) gN dN (online_2_of_B Begd eM dM) dM,
    exact (lines_neq_of_online_offline gN gL) (line_unique_of_pts ef eL fL (by rwa ← this at eM : online e N) fN).symm, },
  have key := angles_add_of_sameside (neq_of_online_offline fL dL) ef.symm fN dN fL eL (sameside_symm (sameside_of_B_not_online_2 Begd eL gL))
    (sameside_symm (sameside_of_B_not_online_2 (B_symm Begd) dN gN)),
  linarith [angle_symm b c a, angle_symm e f g],
end-/

def para (M N : line) : Prop :=  (∀  (e : point), ¬online e M ∨ ¬online e N)

--Euclid I.27
theorem angeqpar {a e f d : point} {L M N : line} (ae : a ≠ e) (ef : e ≠ f) (fd : f ≠ d)
  (aM : online a M) (eM : online e M) (fN : online f N) (dN : online d N)
  (eL : online e L) (fL : online f L) (ang : angle a e f = angle e f d) (adL : diffside a d L) :
  para M N :=
  by sorry /-begin
  intro g,
  by_contra gMN,
  push_neg at gMN,
  have ML : M ≠ L := λ ML, adL.1 (by rwa ML at aM),
  have NL : N ≠ L := λ NL, adL.2.1 (by rwa NL at dN),
  have eN : ¬online e N := λ eN, NL (line_unique_of_pts ef eN fN eL fL),
  have fM : ¬online f M := λ fM, ML (line_unique_of_pts ef eM fM eL fL),
  have gL : ¬online g L := λ gL, ML (line_unique_of_pts (neq_of_online_offline gMN.2 eN) gMN.1 eM gL eL),
  have dg : d ≠ g,
  { intro dg,
    rw dg at *,
    linarith [angle_symm a e f, angle_symm e f g, extang fM gMN.1 aM
    (B_symm (B_of_online_inter  ae (neq_of_online_offline eL gL) (difneq adL) ML aM eM gMN.1 eL adL.2.2))], },
  have ag : a ≠ g,
  { intro ag,
    rw ag at *,
    linarith [extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
    (difsym adL.2.2)))], },
  cases sameside_or_of_diffside adL.2.1 adL.1 gL (difsym adL.2.2) with dgL agL,
  { by_cases Bfdg : B f d g,
    { have Baeg := B_of_online_inter ae (neq_of_online_offline gMN.2 eN).symm ag ML aM eM gMN.1 eL
        (difsym (difsamedif dgL ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (online_3_of_B (B_symm Baeg) gMN.1 eM) (B_symm Baeg),
      linarith [angle_extension_of_B (neq_of_online_offline eM fM).symm Bfdg, angle_symm d f e, angle_symm f e a], },
    by_cases Bfgd : B f g d,
    { have Baeg := B_of_online_inter ae (neq_of_online_offline gMN.2 eN).symm ag ML aM eM gMN.1 eL (difsym (difsamedif dgL
        ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (online_3_of_B (B_symm Baeg) gMN.1 eM) (B_symm Baeg),
      linarith [angle_symm a e f, angle_symm e f g, angle_symm d f e,
        angle_extension_of_B ef.symm Bfgd], },
    cases B_of_three_online_ne fd (neq_of_online_offline fL gL) dg fN dN gMN.2 ,
    exact Bfdg h,
    cases h with Bdfg,
    exact (not_sameside13_of_B123_online2 Bdfg fL) dgL,
    exact Bfgd h, },
  by_cases Beag : B e a g,
  { have ang1 := extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
      (difsym (difsamedif agL adL).2.2))),
    linarith [angle_extension_of_B ef Beag], },
  by_cases Bega : B e g a,
  { have ang1 := extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
      (difsym (difsamedif agL adL).2.2))),
    linarith [angle_extension_of_B ef Bega], },
  cases B_of_three_online_ne ae.symm (neq_of_online_offline eL gL) ag eM aM gMN.1 ,
  exact Beag h,
  cases h with Baeg,
  exact (not_sameside13_of_B123_online2 Baeg eL) agL,
  exact Bega h,
end-/

--Euclid I.29
theorem parapost {a b d e g h : point} {L M N : line} (dh : d ≠ h) (aM: online a M) (gM: online g M)
  (dN: online d N)(hL : online h L) (hN: online h N)
  (gL : online g L) (par : para M N) (Bagb : B a g b) (Begh : B e g h)
  (bdL : sameside b d L) : angle a g h = angle g h d ∧ angle e g b = angle g h d ∧
  angle b g h + angle g h d = 2 * rightangle :=
  by sorry /-begin
  rcases same_length_B_of_ne dh dh.symm with ⟨c, Bdhc, len⟩,
  have hM : ¬online h M, { cases par h, exact h_1, exfalso, exact h_1 hN, },--better way?
  have gN : ¬online g N, { cases par g, exfalso, exact h_1 gM, exact h_1 },--better way?
  have acL : sameside a c L := sameside_of_diffside_diffside (difsamedif bdL ⟨not_online_of_sameside bdL, λ aL, (not_online_of_sameside bdL) (online_3_of_B Bagb aL gL),
    difsym (not_sameside13_of_B123_online2 Bagb gL)⟩) ⟨(not_online_of_sameside (sameside_symm bdL)), λ cL, (not_online_of_sameside (sameside_symm bdL)) (online_3_of_B (B_symm Bdhc) cL hL),
    not_sameside13_of_B123_online2 Bdhc hL⟩,
  have := angle_symm h g b,
  have := angle_symm h g a,
  have := flatsumright aM (online_3_of_B Bagb aM gM) hM Bagb,
  have := flatsumright dN (online_3_of_B Bdhc dN hN) gN Bdhc,
  have key1 : angle a g h = angle g h d,
  { by_contra ang,
    by_cases ang1 : angle g h d < angle a g h, --anything better than the casework?
    { rcases unparallel_postulate (neq_of_online_offline gM hM) (online_3_of_B Bagb aM gM) gM gL hL hN dN bdL
        (by linarith) with ⟨e, eM, eN, junk⟩, -- *** `junk` can be replaced by `-`?
      cases par e,
      exact h_1 eM,
      exact h_1 eN, },
    push_neg at ang1,
    have ang2 : angle a g h < angle g h d := (ne.le_iff_lt ang).mp ang1,--anything better?
    rcases unparallel_postulate (neq_of_online_offline gM hM) aM gM gL hL hN (online_3_of_B Bdhc dN hN) acL
      (by linarith) with ⟨e, eM, eN, junk⟩,
    cases par e, exact h_1 eM, exact h_1 eN, },
  exact ⟨key1, by linarith [vertang hL (online_3_of_B (B_symm Begh) hL gL) (not_online_of_sameside bdL) (B_symm Begh) (B_symm Bagb)],
    by linarith⟩,
end-/

--Euclid I.29
theorem parapostcor {a d g h : point} {L M N : line} (dh : d ≠ h) (aM: online a M) (gM: online g M)
(hN: online h N) (dN: online d N) (hL : online h L)
  (gL : online g L) (par : para M N) (adL : diffside a d L) : angle a g h = angle g h d :=
  by sorry /-begin
  have hg : h ≠ g,
  { intro hg, rw hg at *, cases par g, exact h_1 gM, exact h_1 hN, },
  rcases same_length_B_of_ne (neq_of_online_offline gL adL.1).symm (neq_of_online_offline gL adL.1) with ⟨b, Bagb, junk⟩,
  rcases same_length_B_of_ne hg hg.symm with ⟨e, Bhge, junk⟩,
  exact (parapost dh aM gM dN hL hN gL par Bagb (B_symm Bhge)
    (sameside_of_diffside_diffside ⟨adL.1, (λ bL, adL.1 (online_3_of_B (B_symm Bagb) bL gL)), not_sameside13_of_B123_online2 Bagb gL⟩ adL)).1,
end-/

--Euclid I.29
theorem parapostcor2 {b g h d : point} {L M N : line} (dh : d ≠ h) (bM: online b M) (gM: online g M)
(hN: online h N) (dN: online d N) (hL : online h L)
  (gL : online g L) (par : para M N) (bdL : sameside b d L) : angle b g h + angle g h d = 2 * rightangle  :=
  by sorry /-begin
  have hg : h ≠ g,
  { intro hg, rw hg at *, cases par g, exact h_1 gM, exact h_1 hN, },
  rcases same_length_B_of_ne (neq_of_online_offline gL (not_online_of_sameside bdL)).symm (neq_of_online_offline gL (not_online_of_sameside bdL)) with ⟨a, Bbga, -⟩,
  rcases same_length_B_of_ne hg hg.symm with ⟨e, Bhge, -⟩,
  exact (parapost dh (online_3_of_B Bbga bM gM) gM dN hL hN gL par (B_symm Bbga) (B_symm Bhge)
    bdL).2.2,
end-/

--Euclid I.31
theorem drawpar {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) : ∃ (e : point), ∃ (N : line),online e N ∧ online a N ∧ online b L ∧ online c L∧  para N L :=
  by sorry /-begin
  rcases pt_B_of_ne bc with ⟨d, Bbdc⟩,
  have dL := online_2_of_B Bbdc bL cL,
  rcases line_of_pts d a with ⟨M, dM, aM⟩,
  have bM : ¬online b M := λ bM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bM (online_3_of_B Bbdc bM dM) bL cL),
  rcases angcopy (neq_of_online_offline dL aL).symm (ne_23_of_B Bbdc) dL cL aL aM dM bM with ⟨e, ang, ebM⟩,
  have ae : a ≠ e := λ ae, (not_online_of_sameside ebM) (by rwa ae at aM),
  rcases line_of_pts a e with ⟨N, aN, eN⟩,
  refine ⟨e, N,eN, aN, bL , cL,angeqpar ae.symm (neq_of_online_offline dL aL).symm (ne_23_of_B Bbdc) eN aN dL cL aM dM
    (by linarith [angle_symm e a d, angle_symm a d c]) (difsamedif (sameside_symm ebM)
    ⟨bM, (λ cM, bM (online_3_of_B (B_symm Bbdc) cM dM)), not_sameside13_of_B123_online2 Bbdc dM⟩)⟩,
end-/

theorem parasianar {a b c d : point} {L M N K : line} (aL: online a L) (bL: online b L)
 (cM: online c M) (dM: online d M) (aK: online a K) (cK: online c K) (bN: online b N) (dN: online d N)
 (par1 : para L M) (par2 : para K N) :
  length a b = length c d ∧ angle c a b = angle b d c ∧ area c a b = area b d c :=
  by sorry /-begin
  have ab : a ≠ b := neq_of_online_offline aK (online_of_online_para' bN par2),
  have cd : c ≠ d := neq_of_online_offline cK (online_of_online_para' dN par2),
  have cb : c ≠ b := neq_of_online_offline cM (online_of_online_para bL par1),
  have ca : c ≠ a := neq_of_online_offline cM (online_of_online_para aL par1),
  rcases line_of_pts c b with ⟨O, cO, bO⟩,
  have adO := not_sameside_of_sameside_sameside bL bO bN aL cO dN
    (sameside_of_online_online_para' cM dM par1) (sameside_of_online_online_para aK cK par2),
  have aO : ¬online a O,
  { intro aO, have := line_unique_of_pts ab aL bL aO bO, rw this at par1, cases par1 c,
    exact h cO, exact h cM, },
  have dO : ¬online d O,
  { intro dO, have := line_unique_of_pts cd cO dO cM dM, rw this at *, cases par1 b,
    exact h bL, exact h bO, },
    have ang1:= parapostcor cd.symm aL bL cM dM cO bO par1 ⟨aO, dO, adO⟩,
  have ang2 := parapostcor ca.symm dN bN cK aK cO bO (para_symm par2) ⟨dO, aO, difsym adO⟩,
  have key := asa cb cO bO aO (length_symm b c) (by linarith [angle_symm c b d] : angle c b d = angle b c a)
    (by linarith [angle_symm d c b]),
  exact ⟨by linarith [length_symm c d], key.2.2.symm, (area_eq_of_SSS (len_symm2_of_len key.1) key.2.1 (length_symm c b)).symm⟩,
end-/

--Euclid I.35
theorem parallelarea1 {a b c d e f : point} {L M K N O P : line}
 (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
 (par1 : para L M)
  (par3 : para K N) (par4 : para O P) (Baed : B a e d) :
  area b a d + area d b c = area c f e + area e c b :=
  by sorry /-begin
  have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
  have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
  have eP := online_of_online_para eO par4,
  have dfM := sameside_of_online_online_para dL fL par1,
  have edM := sameside_of_online_online_para eL dL par1,
  have := parasianar aL dL bM cM aK bK dN cN par1 par3,
  have := parasianar bM cM eL fL bO eO cP fP (para_symm par1) par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM (para_symm par1)) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 (para_symm par1)).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN
      fP cP, rw ← NP at *, exfalso,
      cases B_of_three_online_ne (ne_12_of_B Baed) ad (ne_23_of_B Baed) aL eL dL ,

    linarith [length_sum_of_B h, len_pos_of_nq (ne_12_of_B Baed)],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_12_of_B h)],
    have abN := sameside_of_online_online_para aK bK par3,
    exact (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
   },
  have Bedf : B e d f,
  { cases B_of_three_online_ne (ne_23_of_B Baed) (neq_of_online_offline fP eP).symm df eL dL fL ,
    exact h,
    exfalso,
    cases h with Bdef Befd,
    { cases or.swap (Bbcd_or_Bbdc_of_Babc_Babd af (B_symm Baed) Bdef) with Befa Beaf,
      linarith [length_sum_of_B Befa, length_sum_of_B Baed, length_symm e a, len_pos_of_nq af, length_symm a f, len_pos_of_nq (ne_23_of_B Baed)],
      by_cases bfN : sameside b f N,
      { have dbP := difsym (not_sameside_of_sameside_sameside cM cP cN bM fP dN (sameside_symm dfM) bfN),
        have deP := sameside_symm (sameside_of_B_not_online_2 (B_symm Bdef) fP eP),
        exact (difsamedif deP ⟨(λ dP, eP (online_2_of_B (B_symm Bdef) fP dP)),
          online_of_online_para bO par4, dbP⟩).2.2 (sameside_symm (sameside_of_online_online_para bO eO par4)),
      },
      refine bfN (sameside_symm (sameside_trans (sameside_of_B_not_online_2
      (B_symm (B124_of_B123_B234 (B_symm Beaf) Baed)) dN (online_of_online_para aK par3))
        (sameside_of_online_online_para aK bK par3))),
    },
    linarith [length_sum_of_B Befd, length_sum_of_B Baed, len_pos_of_nq (ne_12_of_B Baed), len_pos_of_nq df, length_symm d f],
  },
  have := area_add_iff_B_mp aL dL eL (online_of_online_para' bM par1) Baed,
  have ebN := sameside_trans (sameside_symm (sameside_of_B_not_online_2 (B_symm Baed) dN (λ eN, (online_of_online_para aK par3)
    (online_3_of_B (B_symm Baed) dN eN)))) (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm (ne_23_of_B Baed) bc eL dL bM cM dN cN edM (sameside_of_online_online_para' bM cM par1) ebN,
  have := parasianar aK bK dN cN aL dL bM cM par3 par1,
  have := length_sum_of_B Baed,
  have := length_sum_of_B Bedf,
  have := area_eq_of_SSS (by linarith : length a e = length d f).symm  (len_symm2_of_len (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm)
    (len_symm2_of_len (parasianar aK bK dN cN aL dL bM cM par3 par1).1).symm,
  have := area_add_iff_B_mp eL fL dL (online_of_online_para' cM par1) Bedf,
  linarith [area_invariant b a d, area_invariant b d a, area_invariant d c b, area_invariant d e b, area_invariant b d e, area_invariant e d c, area_invariant c e d, area_invariant d f c,
    area_invariant c f e, area_invariant c b e],
end-/

--Euclid I.35
theorem parallelarea2 {a b c d e f : point} {L M K N O P : line}
 (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
 (par1 : para L M)
  (par3 : para K N) (par4 : para O P) (Bade : B a d e) :
  area b a d + area d b c = area c f e + area e c b :=
  by sorry /-begin
    have ab := neq_of_online_offline aL (online_of_online_para' bM par1),
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have eP := online_of_online_para eO par4,
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have dc := neq_of_online_offline dL (online_of_online_para' cM par1),
    have ef := neq_of_online_offline eO (online_of_online_para' fP par4),
    have dfM := sameside_of_online_online_para dL fL par1,
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP (para_symm par1) par4,
    have bN:= online_of_online_para bK par3,
  by_cases af : a = f,
  { rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM (para_symm par1)) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 (para_symm par1)).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *, have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    { exfalso,
    cases B_of_three_online_ne (ne_13_of_B Bade) ad (ne_23_of_B Bade).symm aL eL dL ,
      linarith [length_sum_of_B h, len_pos_of_nq (ne_13_of_B Bade)], cases h, linarith [length_sum_of_B h, len_pos_of_nq
        (ne_13_of_B Bade).symm],
         have abN := sameside_of_online_online_para aK bK par3,
         refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
    },
  },
  have Bdef : B d e f,
  { cases B_of_three_online_ne (ne_23_of_B Bade) df ef dL eL fL ,
    exact h,
    exfalso,
    cases h with Bedf Bdfe,
    { by_cases bfN : sameside b f N,
      { have dP : ¬online d P := λ dP, eP (online_3_of_B (B_symm Bedf) fP dP),
        have dbP := difsym (not_sameside_of_sameside_sameside cM cP cN bM
          fP dN (sameside_symm dfM) bfN),
        exact (difsamedif (sameside_of_B_not_online_2 (B_symm Bedf) fP dP) ⟨dP, (online_of_online_para bO par4), dbP⟩).2.2
          (sameside_symm (sameside_of_online_online_para bO eO par4)),
      },
      cases Bbcd_or_Bbdc_of_Babc_Babd af (B_symm Bade) Bedf with Bdaf Bdfa,
      linarith [length_sum_of_B Bdaf, length_sum_of_B Bedf, len_pos_of_nq (ne_23_of_B Bade).symm, len_pos_of_nq af, length_symm a d],
      have fN := λ fN, (online_of_online_para aK par3) (online_3_of_B Bdfa dN fN),
      refine (difsamedif (sameside_symm (sameside_of_online_online_para aK bK par3)) ⟨bN, fN, bfN⟩).2.2
        (sameside_symm (sameside_of_B_not_online_2 Bdfa dN fN)),
    },
    have Bfda := Bbcd_of_Babc_Bacd (B_symm Bdfe) (B_symm Bade),
    by_cases bfN : sameside b f N,
    exact (not_sameside13_of_B123_online2 Bfda dN) (sameside_symm (sameside_trans (sameside_symm (sameside_of_online_online_para aK bK par3)) bfN)),
      have fN := λ fN, (online_of_online_para aK par3) (online_3_of_B Bfda fN dN),
    exact (not_sameside13_of_B123_online2 Bdfe fP) (sameside_trans (sameside_of_sameside_not_sameside
      bc.symm cM cN cP bM dN fP fN dfM bfN) (sameside_of_online_online_para bO eO par4)),
  },
  have dO := λ dO, (online_of_online_para' fP par4) (online_3_of_B Bdef dO eO),
  have eN := λ eN, (online_of_online_para aK par3) (online_3_of_B (B_symm Bade) eN dN),
  have cdO := (difsamedif (sameside_symm (sameside_of_online_online_para' cP fP par4))
    ⟨(online_of_online_para' fP par4), dO, difsym (not_sameside13_of_B123_online2 Bdef eO)⟩).2.2,
    have beN := (difsamedif (sameside_of_online_online_para aK bK par3) ⟨(online_of_online_para aK par3), eN,
    (not_sameside13_of_B123_online2 Bade dN)⟩).2.2,
  have beN := (difsamedif (sameside_of_online_online_para aK bK par3) ⟨(online_of_online_para aK par3), eN,
    (not_sameside13_of_B123_online2 Bade dN)⟩).2.2,
  rcases pt_of_lines_inter (lines_inter_of_not_sameside bO eO beN) with ⟨g, gN, gO⟩,
  have Bbge := B_of_online_inter (neq_of_online_offline gN bN).symm
    (neq_of_online_offline gN eN) (neq_of_online_offline bM (online_of_online_para' eL (para_symm par1)))
    (lines_neq_of_online_offline eO eN) bO gO eO gN  beN,
  have Bcgd := B_of_online_inter  (neq_of_online_offline gO (online_of_online_para' cP par4)).symm
  (neq_of_online_offline gO dO) dc.symm (lines_neq_of_online_offline eO eN).symm
    cN gN dN gO  cdO,
  have := parasianar aK bK dN cN aL dL bM cM par3 par1,
  have := length_sum_of_B Bade,
  have := length_sum_of_B Bdef,
  have := area_eq_of_SSS (by linarith : length a e = length d f).symm  (len_symm2_of_len (parasianar bO eO cP fP bM cM eL fL par4 (para_symm par1)).1.symm)
    (len_symm2_of_len (parasianar aK bK dN cN aL dL bM cM par3 par1).1).symm,
  have := area_add_iff_B_mp bO eO gO dO Bbge,
  have := area_add_iff_B_mp bO eO gO (λ cO, dO (online_3_of_B Bcgd cO gO)) Bbge,
  have := area_add_iff_B_mp cN dN gN (λ bN, eN (online_3_of_B Bbge bN gN)) Bcgd,
  have := area_add_iff_B_mp cN dN gN eN Bcgd,
  have := area_add_iff_B_mp aL eL dL (online_of_online_para' bM par1) Bade,
  have := area_add_iff_B_mp dL fL eL (online_of_online_para' cM par1) Bdef,
  linarith [area_invariant d c f, area_invariant c e f, area_invariant d e c, area_invariant c d e, area_invariant a b e, area_invariant a d b, area_invariant e g d, area_invariant d e g,
    area_invariant c b d, area_invariant d c b, area_invariant b g c, area_invariant c b g, area_invariant e c b, area_invariant b e c],
end-/

--Euclid I.35
theorem parallelarea3 {a b c d e f : point} {L M K N O P : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
(par1 : para L M)
  (par3 : para K N) (par4 : para O P) (Bdae : B d a e) :
  area b a d + area d b c = area c f e + area e c b :=
  by sorry /-begin
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have ef := neq_of_online_offline eO (online_of_online_para' fP par4),
    have eP := online_of_online_para eO par4,
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP (para_symm par1) par4,
  by_cases af : a = f,
  {
    rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM (para_symm par1)) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 (para_symm par1)).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    exfalso,
    cases B_of_three_online_ne (ne_23_of_B Bdae) ad (ne_13_of_B Bdae).symm aL eL dL ,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_23_of_B Bdae)],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_23_of_B Bdae).symm],
    have abN := sameside_of_online_online_para aK bK par3,
    refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
  },
  have key : B d f a ∨ B d a f,
  { by_contra key, push_neg at key,
    cases B_of_three_online_ne df (ne.symm ad) (ne.symm af) dL fL aL ,
    exact key.1 h,
    cases h,
    linarith [length_sum_of_B (B124_of_B123_B234 h Bdae), length_sum_of_B Bdae, length_symm a d, length_symm e f, len_pos_of_nq (ne_23_of_B Bdae),
      len_pos_of_nq (ne.symm df)],
    exact key.2 h,
  },
  cases key,
  have := parallelarea1 dL aL cM bM fL eL dN cN aK bK cP fP bO eO par1 (para_symm par1) (para_symm par3) (para_symm par4) key,
  have := quadarea_comm (ne_13_of_B key).symm bc aL dL bM cM dN
    cN (sameside_of_online_online_para aL dL par1) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm ef bc eL fL bM cM fP cP
    (sameside_of_online_online_para' eL fL (para_symm par1)) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para' eO bO (para_symm par4)),
  linarith [area_invariant b a d, area_invariant d b a, area_invariant d b c, area_invariant c b e, area_invariant c b a, area_invariant b e f, area_invariant f b e, area_invariant f b c],
  have := parallelarea2 dL aL cM bM fL eL dN cN aK bK cP fP bO eO par1 (para_symm par1) (para_symm par3) (para_symm par4) key,
  have := quadarea_comm (ad) bc aL dL bM cM dN
    cN (sameside_of_online_online_para aL dL par1) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm ef bc eL fL bM cM fP cP
    (sameside_of_online_online_para' eL fL (para_symm par1)) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para' eO bO (para_symm par4)),
  linarith [area_invariant b a d, area_invariant d b a, area_invariant d b c, area_invariant c b e, area_invariant c b a, area_invariant b e f, area_invariant f b e, area_invariant f b c],
end-/

theorem parallelarea {a b c d e f : point} {L M K N O P : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
(par1 : para L M)
  (par3 : para K N) (par4 : para O P) :
  area b a d + area d b c = area c f e + area e c b :=
  by sorry /-begin
    have ab := neq_of_online_offline aL (online_of_online_para' bM par1),
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have eP := online_of_online_para eO par4,
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP (para_symm par1) par4,
  by_cases af : a = f,
  {
   rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM (para_symm par1)) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 (para_symm par1)).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases ed : e = d, { rw ed at *, linarith, },
  by_cases df : d = f,
  {
    rw ← df at *, have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    by_cases ae : a ≠ e,
    { exfalso,
      cases B_of_three_online_ne ae ad ed aL eL dL ,
      linarith [length_sum_of_B h, len_pos_of_nq ae],
      cases h,
      linarith [length_sum_of_B h, len_pos_of_nq ae.symm],
      have abN := sameside_of_online_online_para aK bK par3,
      refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
    },
    push_neg at ae,
    rw ae at *,
    have := quadarea_comm ad bc eL fL bM cM fP cP
      (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM (para_symm par1)) (sameside_of_online_online_para aK bK par3),
    linarith [area_invariant c b e, area_invariant d c b, area_invariant b d e, area_invariant d e b],
  },
  by_cases ae : a = e,
  { exfalso,
    rw ← ae at *,
    have OK := line_unique_of_pts ab eO bO aK bK,
    rw OK at *,
    cases B_of_three_online_ne ad af df aL dL fL ,
    linarith [len_pos_of_nq df, length_sum_of_B h],
    cases h,
    exact (difsamedif (sameside_symm (sameside_of_online_online_para' cP fP par4)) ⟨(online_of_online_para' fP par4),
      (online_of_online_para' dN par3), difsym (not_sameside13_of_B123_online2 h aK)⟩).2.2 (sameside_symm (sameside_of_online_online_para' dN cN par3)),
    linarith [len_pos_of_nq df, length_symm d f, length_sum_of_B h],
  },
  cases B_of_three_online_ne ae ad ed aL eL dL ,
  exact parallelarea1 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 (para_symm par1) par3 par4 h,
  cases h,
  exact parallelarea3 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 (para_symm par1) par3 par4 (B_symm h),
  exact parallelarea2 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 (para_symm par1) par3 par4 h,
end-/

--Lemma for I.37
theorem parallelodraw {a d b c : point} {L M N : line} (ad : a ≠ d) (bc : b ≠ c) (aN : online a N) (cN : online c N)
  (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
  (par : para L M) (bdN : ¬sameside b d N) :
  ∃ (e : point) (P : line), online e P ∧ online b P ∧ online e L∧  para P N ∧ para L M ∧ B d a e :=
  by sorry /-begin
  rcases line_of_pts a b with ⟨O, aO, bO⟩,
  have bN := λ bN, (online_of_online_para aL par) (by rwa (line_unique_of_pts bc bN cN bM cM) at aN),
  rcases same_length_B_of_ne_four ad.symm bc with ⟨e, Bdae, len⟩,
  have dcO := sameside_of_sameside_not_sameside ad aL aN aO dL cN bO bN (sameside_symm (sameside_of_online_online_para' bM cM par)) (difsym bdN),
  have deO := not_sameside13_of_B123_online2 Bdae aO,
  have dO := not_online_of_sameside dcO,
  have ecO := (difsamedif dcO ⟨dO, λ eO, dO (online_3_of_B (B_symm Bdae) eO aO), deO ⟩),
  have := parapostcor (ne_23_of_B Bdae).symm cM bM aL (online_3_of_B Bdae dL aL) aO bO (para_symm par) ecO,
  have eb := (neq_of_online_offline (online_3_of_B Bdae dL aL) (online_of_online_para' bM par)),
  have := sas len (length_symm a b) (by linarith [angle_symm e a b]),
  rcases line_of_pts e b with ⟨P, eP, bP⟩,
  have := angeqpar eb (neq_of_online_offline aN bN).symm (neq_of_online_offline aL (online_of_online_para' cM par))  eP
    bP aN cN bO aO (by linarith [angle_symm e b a]) ⟨ecO.2.1, ecO.1, difsym ecO.2.2⟩ ,
  refine ⟨e, P, eP,bP,(online_3_of_B Bdae dL aL),this, par, Bdae⟩,
end-/

--Euclid I.37
theorem triarea {a d b c : point} {L M : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
(par : para L M) :
  area a b c = area d b c :=
  by sorry /-begin
  by_cases ad : a = d,
  rw ad,
  by_cases bc : b= c,
  rw bc,
  linarith [area_invariant a c c, area_invariant c a c, area_invariant d c c, area_invariant c d c, degenerate_area c a, degenerate_area c d],
  rcases line_of_pts a c with ⟨N, aN, cN⟩,
  rcases line_of_pts b d with ⟨Q, bQ, dQ⟩,
  rcases line_of_pts d c with ⟨K, dK, cK⟩,
  rcases line_of_pts a b with ⟨O, aO, bO⟩,
  have bN := λ bN, (online_of_online_para aL par) (by rwa (line_unique_of_pts bc bN cN bM cM) at aN),
  by_cases bdN : ¬sameside b d N,
  { rcases parallelodraw ad bc aN cN aL dL bM cM par bdN with ⟨e, P, eP, bP, eL, par1, par2, Bdae⟩,

    rcases parallelodraw (ne.symm ad) (ne.symm bc) dQ bQ dL aL cM bM par
      (difsym (not_sameside_of_sameside_sameside dL dQ dK aL bQ cK (sameside_of_online_online_para' bM cM par)
      (sameside_symm (sameside_of_sameside_not_sameside (λ cb, bc cb.symm) cM cN cK
      bM aN dK (λ dN, (online_of_online_para eP par1)
      (online_3_of_B Bdae dN aN)) (sameside_of_online_online_para aL dL par) bdN )))) with ⟨f, R,fR,cR,fL, par3, par4, Badf⟩,
    have := parallelarea eL aL bM cM dL fL eP bP aN cN bQ dQ cR fR par2 (para_symm par4) par1 (para_symm par3),
    have := parasianar eL aL bM cM eP bP aN cN par2 par1,
    have := parasianar fL dL cM bM fR cR dQ bQ par4 par3,
    linarith [area_invariant a c b, area_invariant d b c],
  },
  push_neg at bdN,
  rcases parallelodraw (ne.symm ad) bc dK cK dL aL bM cM par (not_sameside_of_sameside_sameside cM cK cN bM dK aN
    (sameside_symm (sameside_of_online_online_para aL dL par)) bdN) with ⟨e, P, eP, bP, eL, par1, par2, Bade⟩,
  rcases parallelodraw ad (ne.symm bc) aO bO aL dL cM bM par (difsym (not_sameside_of_sameside_sameside aL aO aN dL bO cN
    (sameside_of_online_online_para' bM cM par) (sameside_symm bdN))) with ⟨f, R,fR,cR,fL, par3, par4, Bdaf⟩,
  have := parallelarea eL dL bM cM aL fL eP bP dK cK bO aO cR fR par (para_symm par) par1 (para_symm par3),
  have := parasianar eL dL bM cM eP bP dK cK par2 par1,
  have := parasianar fL aL cM bM fR cR aO bO par4 par3,
  linarith [area_invariant a c b, area_invariant d b c],
end-/

--Euclid I.41
theorem paratri {a d b c e : point} {L M N K : line} (eL : online e L)
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
(aN: online a N) (bN: online b N) (dK: online d K) (cK: online c K)
(par1 : para L M) (par2 : para N K) : area a d c + area a b c = 2 * area b e c := sorry
--by linarith [parasianar dK cK aN bN dL aL cM bM (para_symm par2) par1,
--triarea aL eL bM cM par1,  area_invariant a b c, area_invariant c a b, area_invariant e b c, area_invariant e c b]

def square (a b d e: point) : Prop :=
a≠ b ∧ a≠ e ∧ length a b = length d e ∧ length a b = length a d ∧ length a b = length b e ∧
angle d a b = angle a b e ∧ angle d a b = angle a d e ∧ angle d a b = angle d e b

def square_strong (a b d e : point) (L M N O : line) : Prop :=
online a M ∧ online d M ∧ online b O ∧ online e O ∧
online a L ∧ online b L ∧ online d N ∧ online e N ∧
length a b = length d e ∧ length a b = length a d ∧
  length a b = length b e ∧ angle d a b = rightangle ∧ angle a b e = rightangle ∧
  angle a d e = rightangle ∧ angle d e b = rightangle ∧ para M O ∧ para L N

theorem square_strong_of_square {a b c d : point} (sq: square a b c d) : ∃ L M N O, square_strong a b c d L M N O :=
  by sorry /-begin
  unfold square at *,
  unfold square_strong at *,
  rcases line_of_pts a c with ⟨M,aM,cM ⟩ ,
  rcases line_of_pts b d with ⟨O,bO,dO⟩ ,
  rcases line_of_pts a b with ⟨ L,aL,bL⟩,
  rcases line_of_pts c d with ⟨ N,cN,dN⟩ ,
  rcases line_of_pts a d with ⟨X,aX,dX ⟩,
  have := sss (len_symm_of_len sq.2.2.1) (length_symm a d) (by linarith [length_symm a c]),
  have dc : d≠ c,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: c=c),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.1,
  },
  have bd: b≠ d,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: d=d),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.2.2.1,
  },
  have ac: a≠ c,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: c=c),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.2.1,
  },
  have bcX: diffside b c X,
  {
    split,
    {
      intro bX,
      cases B_of_three_online_ne bd.symm sq.2.1.symm sq.1.symm dX bX aX with Bdba Bs,
      repeat {by sorry},
    },
    by sorry,
  },
  have lem:= angeqpar sq.1.symm sq.2.1 dc bL aL dN cN aX dX (angle_symm_of_angle this.1.symm).symm bcX,
  have lem2:= angeqpar bd sq.2.1.symm ac bO dO aM cM dX aX (angle_symm_of_angle this.2.2.symm).symm bcX,
  have := parapostcor2 ac bO dO cM aM cN dN lem2 (sameside_of_online_online_para bL aL lem),
  have := angle_symm b d c,
  have := angle_symm d c a,
  refine ⟨L,M,N,O,aM,cM,bO,dO,aL,bL,cN,dN,sq.2.2.1,sq.2.2.2.1,sq.2.2.2.2.1,by linarith, by linarith,
    by linarith,by linarith,para_symm lem2, lem ⟩,
end-/

--Euclid I.46
theorem drawsq {a b g : point} {L : line} (ab : a ≠ b)
  (aL : online a L) (bL : online b L)
  (gL : ¬online g L) : ∃ (d e : point), ∃ (M N O : line),
  square_strong a b d e L M N O ∧  ¬sameside d g L :=
  by sorry /-begin
  rcases same_length_B_of_ne ab.symm ab with ⟨b1, Bbab1, len⟩,
  rcases perplinecor bL (online_3_of_B Bbab1 bL aL) gL Bbab1 with ⟨c, per, per2, cgL⟩,
  rcases same_length_B_of_ne (neq_of_online_offline aL (not_online_of_sameside cgL)).symm ab with ⟨d, Bcad, len1⟩,
  rcases same_length_B_of_ne (ne_23_of_B Bcad) (ne_23_of_B Bcad).symm with ⟨d1, Badd1, lend1⟩,
  rcases circle_of_ne (ne_23_of_B Bcad).symm with ⟨α, acirc, dcen⟩,
  rcases line_of_pts c d with ⟨M, cM, dM⟩,
  have gdL := difsamedif cgL ⟨not_online_of_sameside cgL, (λ dL, (not_online_of_sameside cgL) (online_3_of_B (B_symm Bcad) dL aL)), not_sameside13_of_B123_online2 Bcad aL⟩,
  rcases drawpar ab aL bL gdL.2.1 with ⟨e1, N,e1N,dN,-,-, par1⟩,
  have bM : ¬online b M,
  { intro bM, have := line_unique_of_pts ab aL bL (online_2_of_B Bcad cM dM) bM, rw ← this at cM; exact  (not_online_of_sameside cgL) cM, },
  have eex : ∃ (e : point), online e N ∧ sameside b e M ∧ on_circle e α ∧ d ≠ e,
  { rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online dN (inside_circle_of_center dcen)) with ⟨e2, e3, e2e3,e2N, e3N, e2circ, e3circ⟩ ,
    have Be2de3 : B e2 d e3,
    { have same := (on_circle_iff_length_eq e2circ dcen).mpr e3circ,
      cases B_of_three_online_ne (λ e2d, (not_on_circle_of_inside (inside_circle_of_center dcen)) _)
      e2e3 (λ e3d, (not_on_circle_of_inside (inside_circle_of_center dcen)) (by rwa ← e3d at e3circ)) e2N dN e3N,
      exact h,
      cases h,
      have := length_sum_of_B h,
      linarith [len_pos_of_nq e2e3],
      have := length_sum_of_B h,
      linarith [len_pos_of_nq e2e3, len_symm2_of_len same],
      rwa e2d at e2circ,
      },
  --   by_cases beM : sameside b e2 M,
  --   { refine ⟨e2, e2N, beM, e2circ, by btw⟩, },
  --   have e2M : ¬online e2 M,
  --   { intro e2M,
  --     have := line_unique_of_pts (ne_12_of_B Be2de3) e2M dM e2N dN,
  --     rw this at *,
  --     exact (online_of_online_para' aL par1) (online_2_of_B Bcad cM dM), },
  --   have e3M := λ e3M, e2M (online_3_of_B (B_symm Be2de3) e3M dM),
  --   refine ⟨e3, e3N, sameside_of_diffside_diffside ⟨e2M, bM, difsym beM⟩ ⟨e2M, e3M, not_sameside13_of_B123_online2 Be2de3 dM⟩, e3circ,
  --     (ne_23_of_B Be2de3)⟩, 
    by sorry, },
  rcases eex with ⟨e, eN, beM, ecirc, de⟩,
  rcases line_of_pts e b with ⟨O, eO, bO⟩,
  rcases line_of_pts e a with ⟨P, eP, aP⟩,
  rcases same_length_B_of_ne de.symm de with ⟨e4, Bede4, lene4⟩,
  have bdP := not_sameside_of_sameside_sameside aL aP (online_2_of_B Bcad cM dM) bL eP dM (sameside_symm (sameside_of_online_online_para dN eN par1)) beM,
  have bP : ¬online b P,
  {
    intro bP,rw (line_unique_of_pts ab aL bL aP bP) at *,
    exact (online_of_online_para' eP par1) eN,
  },
  have dP : ¬online d P,
  { intro dP,
    have := line_unique_of_pts de dN eN dP eP,
    rw this at *,
    exact (online_of_online_para aL (para_symm par1)) aP,
  },
  have := (on_circle_iff_length_eq acirc dcen).mpr ecirc,
  have := parapostcor de  bL aL eN dN  eP aP (para_symm par1) ⟨bP, dP, bdP⟩,
  have := sas (length_symm a e) (len_symm2_of_len (by linarith [length_symm d a] : length d e = length b a)).symm
    (by linarith [angle_symm b a e]),
  have par2 := angeqpar (neq_of_online_offline eP bP).symm (neq_of_online_offline eN (online_of_online_para' aL par1)) (neq_of_online_offline aP dP)
     bO eO (online_2_of_B Bcad cM dM) dM eP aP (by linarith [angle_symm a e b]) ⟨bP, dP, bdP⟩,
  have := parapost (neq_of_online_offline eP bP).symm (online_3_of_B Badd1 (online_2_of_B Bcad cM dM) dM) dM bO eN eO  dN (para_symm par2) (B_symm Badd1) (B_symm Bede4)
    (sameside_of_online_online_para' aL bL par1),
  have := flatsumright cM dM bM Bcad,
  have := angle_symm b a d,
  have := angle_symm d e b,
  have := angle_symm a d e,
  have := parasianar aL bL dN eN (online_2_of_B Bcad cM dM) dM bO eO (para_symm par1) (para_symm par2)  ,
  refine ⟨d, e, M, N, O,⟨ online_2_of_B Bcad cM dM,dM,bO,eO,aL,bL,dN,eN, this.1,by linarith[length_symm a b],
  by linarith [length_symm e b, length_symm a b],by linarith,by linarith,by linarith,by linarith, para_symm par2, para_symm par1⟩, difsym gdL.2.2⟩,
end-/

--Euclid I.47
theorem pythagorasdraw {a b c : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cN : ¬online c N) : ∃ (f g h k d e : point) (L M O P Q R S T U V W : line),
  square_strong b a f g N W V U ∧ square_strong c a k h M R S T ∧ square_strong b c d e L Q P O ∧ ¬sameside f c N ∧
  ¬sameside k b M ∧ ¬sameside d a L :=
  by sorry /-begin
  rcases line_of_pts a c with ⟨M, aM, cM⟩,
  rcases line_of_pts b c with ⟨L, bL, cL⟩,
  rcases drawsq ab.symm bN aN cN with ⟨f, g, W, V, U, sq1, fcN⟩,
  rcases drawsq (neq_of_online_offline aN cN).symm cM aM (λ bM, (lines_neq_of_online_offline cM cN) (line_unique_of_pts ab aM bM aN bN)) with
    ⟨k, h, R, S,T, sq2, hbM⟩,
  rcases drawsq (neq_of_online_offline bN cN) bL cL (λ aL, (lines_neq_of_online_offline cL cN) (line_unique_of_pts ab aL bL aN bN)) with
    ⟨d, e, Q, P, O, sq3, daL⟩,
  refine ⟨f, g, h, k, d, e, L, M, O, P, Q, R, S,T, U, V, W, sq1, sq2, sq3, fcN, hbM, daL⟩,
end-/

theorem pythlem0 {a b c d : point} {L : line} (bc : b ≠ c) (bd : b ≠ d) (bL : online b L)
  (cL : online c L) (dL : online d L) (aL : ¬online a L) (ang : angle a b c = rightangle) :
  angle a b d = rightangle :=
  by sorry /-begin
  by_cases cd : c = d,
  rwa ← cd,
  cases B_of_three_online_ne bc bd cd bL cL dL ,
  have := angle_extension_of_B (neq_of_online_offline bL aL) h,
  have := angle_symm a b c,
  have := angle_symm a b d,
  linarith,
  cases h,
  have := flatsumright cL dL aL h,
  linarith,
  have := angle_extension_of_B (neq_of_online_offline bL aL) h,
  have := angle_symm a b c,
  have := angle_symm a b d,
  linarith,
end-/

--Euclid I.47/Generalization of I.13
theorem pythlem {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (ang : rightangle ≤ angle c a b) :
  ∃ (m : point), angle a m b = rightangle ∧ angle a m c = rightangle ∧ B b m c :=
  by sorry /-begin
  rcases perppointnon aL with ⟨h, m, g, hL, mL, gL, Bhmg, ang1⟩,
  have mb : m ≠ b,
  { intro mb,
    rcases line_of_pts b a with ⟨M, bM, aM⟩,
    have cM : ¬online c M,
    { intro cM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mb at *,
    rcases same_length_B_of_ne (neq_of_online_offline bL aL) (neq_of_online_offline bL aL).symm with ⟨a1, Bbaa1, junk⟩,
    have := flatsumright bM (online_3_of_B Bbaa1 bM aM) cM Bbaa1,
    have := extangcor cM bM (online_3_of_B Bbaa1 bM aM) Bbaa1,
    have := angle_symm c b a,
    by_cases gcM : sameside g c M,
    { by_cases gc : g = c,
      rw gc at *,
      linarith,
      have := angle_extension_of_ss (neq_of_online_offline bL aL) gc bM aM bL gL cL gcM,
      have := angle_symm a b g,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts ((ne_12_of_B Bhmg).symm) bL hL bM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts (ne_23_of_B Bhmg) bL gL bM gM).symm, },
    have hcM := sameside_symm (sameside_of_diffside_diffside ⟨gM, cM, gcM⟩ ⟨gM, hM, difsym (not_sameside13_of_B123_online2 Bhmg bM)⟩),
    by_cases hc : h = c,
    rw hc at *,
    linarith,
    have := angle_extension_of_ss (neq_of_online_offline bL aL) hc bM aM bL hL cL hcM,
    have := angle_symm a b h,
    linarith, },
  have mc : m ≠ c,
  { intro mc,
    rcases line_of_pts c a with ⟨M, cM, aM⟩,
    have bM : ¬online b M,
    { intro bM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mc at *,
    rcases same_length_B_of_ne (neq_of_online_offline cL aL) (neq_of_online_offline cL aL).symm with ⟨a1, Bcaa1, junk⟩,
    have := flatsumright cM (online_3_of_B Bcaa1 cM aM) bM Bcaa1,
    have := extangcor bM cM (online_3_of_B Bcaa1 cM aM) Bcaa1,
    have := angle_symm b c a,
    have := angle_symm c a b,
    by_cases gbM : sameside g b M,
    { by_cases gb : g = b,
      rw gb at *,
      linarith,
      have := angle_extension_of_ss (neq_of_online_offline cL aL) gb cM aM cL gL bL gbM,
      have := angle_symm a c g,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts ((ne_12_of_B Bhmg).symm) cL hL cM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts (ne_23_of_B Bhmg) cL gL cM gM).symm, },
    have hbM := sameside_symm (sameside_of_diffside_diffside ⟨gM, bM, gbM⟩ ⟨gM, hM, difsym (not_sameside13_of_B123_online2 Bhmg cM)⟩),
    by_cases hb : h = b,
    rw hb at *,
    linarith,
    have := angle_extension_of_ss (neq_of_online_offline cL aL) hb cM aM cL hL bL hbM,
    have := angle_symm a c h,
    linarith, },
  have ang2 := pythlem0 (ne_23_of_B Bhmg) mb mL gL bL aL ang1.2,
  have ang3 := pythlem0 (ne_23_of_B Bhmg) mc mL gL cL aL ang1.2,
  cases B_of_three_online_ne mb mc bc mL bL cL  with Bmbc hs,
  exfalso,
  rcases same_length_B_of_ne (ne.symm mb) (mb) with ⟨m1, Bbmm1, junk⟩,
  have := flatsumright bL (online_3_of_B Bbmm1 bL mL) aL Bbmm1,
  have := extangcor aL bL (online_3_of_B Bbmm1 bL mL) Bbmm1,
  have := flatsumright mL cL aL Bmbc,
  rcases line_of_pts b a with ⟨M, bM, aM⟩,
  have cM := λ cM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm,
  rcases same_length_B_of_ne (neq_of_online_offline bL aL) (neq_of_online_offline bL aL).symm with ⟨a1, Bbaa1, junk⟩,
  have := flatsumright bM (online_3_of_B Bbaa1 bM aM) cM Bbaa1,
  have := extangcor cM bM (online_3_of_B Bbaa1 bM aM) Bbaa1,
  have := angle_symm c b a,
  linarith,
  cases hs.swap with Bmcb Bbmc,
  rcases same_length_B_of_ne (ne.symm mc) (mc) with ⟨m1, Bcmm1, junk⟩,
  have := flatsumright cL (online_3_of_B Bcmm1 cL mL) aL Bcmm1,
  have := extangcor aL cL (online_3_of_B Bcmm1 cL mL) Bcmm1,
  have := flatsumright mL bL aL Bmcb,
  rcases line_of_pts c a with ⟨M, cM, aM⟩,
  have bM := λ bM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc.symm cL bL cM bM).symm,
  rcases same_length_B_of_ne (neq_of_online_offline cL aL) (neq_of_online_offline cL aL).symm with ⟨a1, Bcaa1, junk⟩,
  have := flatsumright cM (online_3_of_B Bcaa1 cM aM) bM Bcaa1,
  have := extangcor bM cM (online_3_of_B Bcaa1 cM aM) Bcaa1,
  have := angle_symm b c a,
  have := angle_symm b a c,
  linarith,
  refine ⟨m, ang2, ang3, Bbmc⟩,
end-/

--Euclid I.47
theorem pythagoras {a b c f g h k d e : point} {L M N O P Q R S T U V W : line} (bc : b ≠ c)
  (aL : ¬online a L) (ang : angle c a b = rightangle) (sq1 : square_strong b a f g N W V U)
  (sq2 : square_strong c a k h M R S T) (sq3 : square_strong b c d e L Q P O) (fcN : ¬sameside f c N)
  (kbM : ¬sameside k b M) (daL : ¬sameside d a L) :
  area d b e+ area e c b = area a b f + area a g f + area a h k + area a c k :=
  by sorry /-begin
  unfold square_strong at sq3,
  unfold square_strong at sq2,
  unfold square_strong at sq1,
  have bL := online_1_1_of_square sq3,
  have cL := online_2_1_of_square sq3,
  have dP := online_3_3_of_square sq3,
  have eP := online_4_3_of_square sq3,
  have eO := online_4_4_of_square sq3,
  have sq3par1:= (para_1_3_of_square sq3),
  have sq2par1:= (para_1_3_of_square sq2),
  have sq1par1:= (para_1_3_of_square sq1),
  have sq3par2:= para_2_4_of_square sq3,
  have sq1par2:= para_2_4_of_square sq1,
  have sq2par2:= para_2_4_of_square sq2,
  have bP := (online_of_online_para bL sq3par1),
  have bN := online_1_1_of_square sq1,
  have aN := online_2_1_of_square sq1,
  have cM := online_1_1_of_square sq2,
  have aM := online_2_1_of_square sq2,
  have aU := online_2_4_of_square sq1,
  have gU := online_4_4_of_square sq1,
  have aT := online_2_4_of_square sq2,
  have hT := online_4_4_of_square sq2,
  have bW := online_1_2_of_square sq1,
  have fW := online_3_2_of_square sq1,
  have cR := online_1_2_of_square sq2,
  have kR := online_3_2_of_square sq2,
  have kS := online_3_3_of_square sq2,
  have fV := online_3_3_of_square sq1,
  have gV := online_4_3_of_square sq1,
  have hS := online_4_3_of_square sq2,
  have kM := (online_of_online_para kS (para_symm sq2par1)),
  have fN := (online_of_online_para fV (para_symm sq1par1)),
  have cP := (online_of_online_para cL  sq3par1),
  have ec := (neq_of_online_offline eP cP),
  have db := (neq_of_online_offline dP bP),
  have dL := (online_of_online_para dP  (para_symm sq3par1)),
  have eL := (online_of_online_para eP  (para_symm sq3par1)),
  have cd := neq_of_online_offline cL dL,
  have ca := (neq_of_online_offline cL aL),
  have ba := (neq_of_online_offline bL aL),
  have eQ := (online_of_online_para eO  (para_symm sq3par2)),
  have dQ := online_3_2_of_square sq3,
  have bQ := online_1_2_of_square sq3,
  have dO := (online_of_online_para dQ  sq3par2),
  have cO := online_2_4_of_square sq3,
  have de := neq_of_online_offline dQ eQ,
  have bf := neq_of_online_offline bN fN,
  have ck := neq_of_online_offline cM kM,
  rcases pythlem bc bL cL aL (by linarith) with ⟨m, ang1, ang2, Bbmc⟩,
  have mL := (online_2_of_B Bbmc bL cL),
  have ma := (neq_of_online_offline mL aL),
  have md := neq_of_online_offline mL dL,
  have me := neq_of_online_offline mL eL,
  rcases line_of_pts m a with ⟨X, mX, aX⟩,
  have mP := online_of_online_para mL sq3par1,
  have mQ : ¬online m Q,
  { intro mQ, have := line_unique_of_pts (ne_12_of_B Bbmc) bL mL bQ mQ, rw this at *, exact dL dQ, },
  have mO : ¬online m O,
  { intro mO, have := line_unique_of_pts (ne_12_of_B (B_symm Bbmc)) cL mL cO mO, rw this at *, exact eL eO, },
  have mcQ := sameside_of_B_not_online_2 Bbmc bQ mQ,
  have ceQ := sameside_of_online_online_para' cO eO  sq3par2,
  have meQ := sameside_symm (sameside_trans ceQ (sameside_symm mcQ)),
  have mbP := sameside_of_online_online_para mL bL sq3par1,
  have mbO := sameside_of_B_not_online_2 (B_symm Bbmc) cO mO,
  have bdO := sameside_of_online_online_para bQ dQ sq3par2,
  have mdO := sameside_symm (sameside_trans bdO (sameside_symm mbO)),
  have mcP := sameside_of_online_online_para mL cL sq3par1,
  rcases perppointnon mP with ⟨p1, l, p2, p1P, lP, p2P, Bp1lp2, angs⟩,
  have lm := neq_of_online_offline lP mP,
  rcases line_of_pts l m with ⟨X', lX', mX'⟩,
  have := angle_symm c b d,
  have dl : d ≠ l,
  { intro dl,
    rw ← dl at *,
    rcases same_length_B_of_ne (ne_12_of_B Bbmc).symm (ne_12_of_B Bbmc) with ⟨b1, Bmbb1, junk⟩,
    have := flatsumright mL (online_3_of_B Bmbb1 mL bL) dL Bmbb1,
    have := extangcor dL mL (online_3_of_B Bmbb1 mL bL) Bmbb1,
    have beX' := not_sameside_of_sameside_sameside dQ lX' dP bQ mX' eP meQ (sameside_symm mbP),
    have bX' : ¬online b X',
    { intro bX', have := line_unique_of_pts (ne_12_of_B Bmbb1) mL bL mX' bX', rw this at *, exact dL lX', },
    have eX' : ¬online e X',
    { intro eX', have := line_unique_of_pts (neq_of_online_offline dQ eQ) dP eP lX' eX', rw this at *, exact mP mX', },
    have := parapostcor (ne_12_of_B Bmbb1).symm eP dP mL bL mX' lX' (para_symm sq3par1)  ⟨eX', bX', difsym beX'⟩,
    have := pythlem0 (ne_12_of_B Bp1lp2).symm (neq_of_online_offline dQ eQ) dP p1P eP mP (by linarith),
    have := angle_extension_of_B db.symm Bbmc,
    have := angle_symm e d m,
    have := angle_symm m b d,
    have := angle_symm c b d,
    linarith, },
  have el : e ≠ l,
  { intro el,
    rw ← el at *,
    rcases same_length_B_of_ne (ne_12_of_B (B_symm Bbmc)).symm (ne_12_of_B (B_symm Bbmc)) with ⟨b1, Bmcc1, junk⟩,
    have := flatsumright mL (online_3_of_B Bmcc1 mL cL) eL Bmcc1,
    have := extangcor eL mL (online_3_of_B Bmcc1 mL cL) Bmcc1,
    have cdX' := not_sameside_of_sameside_sameside eO lX' eP cO mX' dP mdO (sameside_symm mcP),
    have cX' : ¬online c X',
    { intro cX', have := line_unique_of_pts (ne_12_of_B Bmcc1) mL cL mX' cX', rw this at *, exact eL lX', },
    have dX' : ¬online d X',
    { intro dX', have := line_unique_of_pts (neq_of_online_offline eO dO) eP dP lX' dX', rw this at *, exact mP mX', },
    have := parapostcor (ne_12_of_B Bmcc1).symm dP eP mL cL mX' lX' (para_symm sq3par1) ⟨dX', cX', difsym cdX'⟩,
    have := pythlem0 (ne_12_of_B Bp1lp2).symm (neq_of_online_offline eO dO) eP p1P dP mP (by linarith),
    have := angle_extension_of_B ec.symm (B_symm Bbmc),
    have := angle_symm d e m,
    have := angle_symm m c e,
    linarith, },
  have eX' : ¬online e X',
  { intro eX', have := line_unique_of_pts el eP lP eX' lX', rw this at *, exact mP mX', },
  have dX' : ¬online d X',
  { intro dX', have := line_unique_of_pts dl dP lP dX' lX', rw this at *, exact mP mX', },
  have := angle_symm d e c,
  have := angle_symm m l d,
  have := angle_symm m l e,
  have ang4 := pythlem0 (ne_12_of_B Bp1lp2).symm el.symm lP p1P eP mP angs.1,
  have ang3 := pythlem0 (ne_12_of_B Bp1lp2).symm dl.symm lP p1P dP mP angs.1,
  have ang5 := pythlem0 de dl dP eP lP bP (by linarith),
  have ang6 := pythlem0 de.symm el eP dP lP cP (by linarith),--sq3.2.2.2.2.2.2.1
  rcases same_length_B_of_ne lm.symm lm with ⟨l', Bmll', junk⟩,
  have := flatsumright mX' (online_3_of_B Bmll' mX' lX') dX' Bmll',
  have := flatsumright mX' (online_3_of_B Bmll' mX' lX') eX' Bmll',
  have ml'P := not_sameside13_of_B123_online2 Bmll' lP,
  have bl'P := difsamedif mbP ⟨mP, (λ l'P, mP (online_3_of_B (B_symm Bmll') l'P lP)), ml'P⟩,
  have cl'P := difsamedif mcP ⟨mP, (λ l'P, mP (online_3_of_B (B_symm Bmll') l'P lP)), ml'P⟩,
  have par2 := (angeqpar db.symm dl (ne_23_of_B Bmll')
    bQ dQ lX' (online_3_of_B Bmll' mX' lX') dP lP (by linarith) bl'P),
  have par3 :=  (angeqpar ec.symm el (ne_23_of_B Bmll')
    cO eO lX' (online_3_of_B Bmll' mX' lX') eP lP (by linarith) cl'P),
  have := parasianar bL mL dP lP bQ dQ mX' lX' sq3par1 par2,
  have := parasianar cL mL eP lP cO eO mX' lX' sq3par1 par3,
  have := length_sum_of_B Bbmc,
  have := parasianar  dP lP bL mL dQ bQ lX' mX' (para_symm sq3par1) par2,
  have := angle_symm b m a,
  have := angle_symm b m l,
  have Blma := rightimpflat (ne_12_of_B Bbmc) bL mL (difsamedif (sameside_of_online_online_para' dP lP sq3par1)
    ⟨dL, aL, daL⟩) (by linarith),
  have Bdle := B_of_length_leq dl el.symm de dP lP eP (by linarith [length_symm m c, length_symm e l]),
  have := (line_unique_of_pts ma mX aX mX' (online_3_of_B Blma lX' mX')),
  rw ← this at *,
  have cN : ¬online c N,
  { intro cN, have := line_unique_of_pts bc bL cL bN cN, rw this at *, exact aL aN, },
  have fgN := sameside_of_online_online_para' fV gV sq1par1,
  have UM : U = M,
  { have := rightimpflat ba bN aN (difsamedif fgN ⟨not_online_of_sameside fgN, cN, fcN⟩) (by linarith [angle_symm b a c]),
    exact line_unique_of_pts (ne_23_of_B this) aU (online_3_of_B this gU aU) aM cM, },
  have khM := sameside_of_online_online_para' kS hS sq2par1,
    have bM : ¬online b M, { intro bM, have := line_unique_of_pts bc bL cL bM cM, rw this at *, exact aL aM, },
  have TN : T = N,
  { have := rightimpflat ca cM aM (difsamedif khM ⟨not_online_of_sameside khM, bM, kbM⟩) (by linarith [angle_symm c a b]),
    exact line_unique_of_pts (ne_23_of_B this) aT (online_3_of_B this hT aT) aN bN, },
  rw TN at *,
  rw UM at *,
  have ang1 : angle a b d = angle f b c,
  { have caW := sameside_of_online_online_para' cM aM sq1par2,
    have faL := sameside_of_sameside_not_sameside bf bW bN bL fW aN cL cN (sameside_symm caW) fcN, --(sameside_symm caW) ⟨cN, not_online_of_sameside fgN, sameside_symm cN⟩,
    have := angles_add_of_sameside bf bc bW fW bL cL faL caW,
    have bdX := sameside_of_online_online_para bQ dQ par2,
    have amQ := sameside_of_online_online_para' aX mX par2,
    have dmN := sameside_of_sameside_not_sameside db.symm bQ bL bN dQ mL aN aL (sameside_symm amQ) daL,
    rcases quadiag db ma dQ bQ mX aX bN aN (sameside_symm bdX)
      (sameside_symm amQ) dmN with
      ⟨y,Y1,Y2, dY1, aY1, bY2, mY2,yY1,yY2, Bbym, Bayd, mY1, bY1, aY2, dY2⟩,
    have yQ : ¬online y Q,
    { intro yQ, have := line_unique_of_pts (ne_23_of_B Bayd) yY1 dY1 yQ dQ, rw this at *, exact bY1 bQ, },
    have yN : ¬online y N,
    { intro yN, have := line_unique_of_pts (ne_12_of_B Bayd) aY1 yY1 aN yN, rw this at *, exact bY1 bN, },
    have := angles_add_of_sameside ba db.symm bN aN bQ dQ
      (sameside_symm (sameside_of_B_not_online_2 (B_symm Bayd) dQ yQ))
      (sameside_symm (sameside_of_B_not_online_2 Bayd aN yN)),
    have := angle_extension_of_B ba (B124_of_B134_B123 Bbmc Bbym),
    have := angle_extension_of_B db.symm (B124_of_B134_B123 Bbmc Bbym),
    have := angle_symm a b y,
    have := angle_symm a b c,
    linarith, },
  have ang2 : angle a c e = angle k c b,
  {
    have baR := sameside_of_online_online_para' bN aN sq2par2,
    have kaL := sameside_of_sameside_not_sameside ck cR cM cL kR aM bL bM (sameside_symm baR) kbM , --(sameside_symm caW) ⟨cN, not_online_of_sameside fgN, sameside_symm cN⟩,
    have := angles_add_of_sameside ck bc.symm cR kR cL bL kaL baR,
    have eaL := difsamedif (sameside_symm (sameside_of_online_online_para' eP dP sq3par1)) ⟨dL, aL, daL⟩,
    have emM := sameside_of_sameside_not_sameside ec.symm cO cL cM eO mL aM aL (sameside_symm (sameside_of_online_online_para' aX mX par3)) eaL.2.2,
    rcases quadiag ec ma eO cO mX aX cM aM (sameside_symm (sameside_of_online_online_para cO eO par3))
      (sameside_symm (sameside_of_online_online_para' aX mX par3)) emM with
      ⟨y,Y1,Y2, eY1, aY1, cY2, mY2,yY1,yY2, Bcym, Baye, mY1, cY1, aY2, eY2⟩,
    have yO : ¬online y O,
    { intro yO, have := line_unique_of_pts (ne_23_of_B Baye) yY1 eY1 yO eO, rw this at *, exact cY1 cO, },
    have yM : ¬online y M,
    { intro yM, have := line_unique_of_pts (ne_12_of_B Baye) aY1 yY1 aM yM, rw this at *, exact cY1 cM, },
    have := angles_add_of_sameside ca ec.symm cM aM cO eO (sameside_symm (sameside_of_B_not_online_2 (B_symm Baye) eO yO)) (sameside_symm (sameside_of_B_not_online_2 Baye aM yM)),
    have := angle_extension_of_B ca (B124_of_B134_B123 (B_symm Bbmc) Bcym),
    have := angle_extension_of_B ec.symm (B124_of_B134_B123 (B_symm Bbmc) Bcym),
    have := angle_symm a c y,
    have := angle_symm a c b,
    linarith, },
  have := sas sq1.2.2.2.2.2.2.2.2.2.1 sq3.2.2.2.2.2.2.2.2.2.1.symm ang1,
  have := area_eq_of_SSS sq1.2.2.2.2.2.2.2.2.2.1 this.1 (len_symm2_of_len sq3.2.2.2.2.2.2.2.2.2.1.symm),
  have := sas sq2.2.2.2.2.2.2.2.2.2.1 (len_symm_of_len sq3.2.2.2.2.2.2.2.2.2.2.1).symm ang2,
  have := area_eq_of_SSS sq2.2.2.2.2.2.2.2.2.2.1 this.1 (len_symm_of_len sq3.2.2.2.2.2.2.2.2.2.2.1.symm),
  have := paratri cM aU gU bW fW aN bN gV fV (para_symm sq1par2) sq1par1,
  have := paratri bN aN hT cR kR aM cM hS kS (para_symm sq2par2) sq2par1,
  have := paratri aX mX lX' bQ dQ mL bL lP dP (para_symm par2) sq3par1,
  have := paratri aX mX lX' cO eO mL cL lP eP (para_symm par3) sq3par1,
  have := quad_add_of_quad_quad bL cL dP eP cO eO Bbmc Bdle (sameside_of_online_online_para bL cL sq3par1)
    (sameside_of_online_online_para' dP eP sq3par1) bdO,
  have := quadarea_comm (ne_12_of_B Bbmc) (ne_12_of_B Bdle) bL mL dP lP mX lX' (sameside_symm mbP)
    (sameside_of_online_online_para' dP lP sq3par1) (sameside_of_online_online_para bQ dQ par2),
  have := quadarea_comm (ne_12_of_B (B_symm Bbmc)) (ne_12_of_B (B_symm Bdle)) cL mL eP lP mX lX' (sameside_symm mcP)
    (sameside_of_online_online_para' eP lP sq3par1) (sameside_of_online_online_para cO eO par3),
  linarith [area_invariant b c f, area_invariant c b k, area_invariant l d b, area_invariant l b d, area_invariant l m b, area_invariant b l m],
end-/


--Simplest statement
theorem pythagorean_theorem {a b c : point} (ang : angle c a b = rightangle) :
  (length a b)^2 + (length a c)^2 = (length b c)^2  :=
  by sorry /-begin
  by sorry,
end-/

------------------------------------------- old API ------------------------------------------------
lemma nq_of_len_pos {a b : point} (length : 0 < length a b) : a ≠ b
  := (not_congr (length_eq_zero_iff)).1 (ne_of_gt length)

theorem sameside_of_diffside_diffside {a b c : point} {L : line} (dsab : diffside a b L) (dsac : diffside a c L) :
  sameside b c L :=(or_iff_right dsac.2.2).mp
  (sameside_or_of_diffside dsab.1 dsab.2.1 dsac.2.1 dsab.2.2)

theorem para_symm {M N : line} (par: para M N) : para N M:= by sorry --λ a, or.swap (par a)

theorem online_of_online_para {a : point} {M N: line}(aM: online a M)(par: para M N): ¬ online a N:=
  by sorry /-begin
  cases par a,exfalso,exact h aM,exact h,
end-/

theorem sameside_of_online_online_para {a b : point} {M N: line} (aM: online a M) (bM: online b M)(par: para M N):
sameside a b N:=
  by sorry /-begin
   by_contra abN, rcases pt_of_lines_inter (lines_inter_of_not_sameside aM bM abN) with ⟨z,zN,zM⟩,
    cases par z, exact h zM, exact h zN,
end

  theorem length_eq_of_ne' (a : point) (bc : b ≠ c) : ∃ (f : point), length a f = length b c := by
by_cases ab : a = b; rw [ab]; exact ⟨c, rfl⟩ --degenerate case
rcases iseqtri_of_ne ab with ⟨d, eqtri⟩
rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩
rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩
use f
calc length a f = length b e := length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 
                                (length_eq_of_oncircle dβ eβ fβ)
     length b e = length b c := (length_eq_of_oncircle bα cα eα).symm
-/