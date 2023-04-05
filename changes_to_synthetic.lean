/-
Here I will note changes made to the axioms and synthetic:

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