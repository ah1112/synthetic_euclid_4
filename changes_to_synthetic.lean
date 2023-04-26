/-
Here I will note changes made to the axioms and synthetic:

--2023/4/24
Got rid of pt_extension_of_ne since it can be deduced from length_eq_B_of_ne

Refactored I.11-14

--2023/4/14
Changed sameside23_of_B123_online1_not_online2 to sameside_of_B_not_online_2

Refactored I.9-10

--2023/4/8
Made an attempt to refactor I.6

Changed
  area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b)
to
  area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a b c ↔ area d a b + area d c b = area d a c)

Changed
  area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 → length b c = length b1 c1 →
    length c a = length c1 a1 → area a b c = area a1 b1 c1
to
  area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 →
  length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1

Desorrified online_ne_of_line

--2023/4/5

Changed 
  pt_on_circle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, b ≠ c →in_circle b α →
  ∃ (a : point), B a b c ∧ on_circle a α
to
  pt_oncircle_of_inside_ne : ∀ {a b : point}, ∀ {α : circle}, a ≠ b → in_circle b α →
  ∃ (c : point), B a b c ∧ on_circle c α

Defined isosceles triangles as iso_tri

Changed same_length_B_of_ne_le to B_length_eq_of_ne_lt

Changed same_length_B_of_ne_four to length_eq_B_of_ne_four. The length in the conclusion is off
by a .symm from the original

Changed 
  theorem same_length_B_of_ne {a b c : point} (hab : a ≠ b) (hbc : b ≠ c) :
  ∃ (p : point), B a b p ∧ length b p = length c b
to
  theorem length_eq_B_of_ne (ab : a ≠ b) (bc : b ≠ c) :
  ∃ (d : point), B a b d ∧ length b c = length b d

Changed difsamedif to diffside_of_sameside_diffside

Ported Euclid I.1-5

Unsorrified online_of_line. Why is the indentation so delicate for this?

Swapped variables in diffside_of_not_online so that we obtain sameside a b L and inputs
are alphabetical
  Before:
    diffside_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
    ∃ (a : point), ¬online a L ∧ ¬sameside a b L
  After:
    diffside_of_not_online : ∀ {L : line}, ∀ {a : point}, ¬online a L →
    ∃ (b : point), ¬online b L ∧ ¬sameside a b L

--2023/4/4

Removed all imports except "Euclid.synthetic_axioms", since the axioms import ℝ along with Finite
  already

Changed cen_circ to center_circle

Changed oncircle to on_circle

Changed in_circ to in_circle

Changed
  (circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), on_circle b α ∧ center_circle a α)
to
  (circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ on_circle b α)
i.e. obtain the center before the point on the circle (also alphabetically more intuitive)

Changed incircle_iff_length_lt to in_circle_iff_length_lt to match on_circle_iff_length_eq

Swapped the first two arguments in in_circle_iff_length_lt
  (in_circle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α → 
  (length a c < length a b ↔ in_circle c α))

Swapped the first two arguments in on_circle_iff_length_eq
  (on_circle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α → 
  (length a b = length a c ↔ on_circle c α))

-/