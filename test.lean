import SyntheticEuclid4.tactics
open incidence_geometry
variable [i: incidence_geometry]

lemma test_perm1 {a b : point} : area a b b = area b b a ∧ area a b c + area e d f = area a c b + area d f e ∧ area a b c + area e d f = area a c b + area f d e := by splitAll; all_goals perm only [area]

lemma test_perm2 {a b c: point} : area b a c + area c b a = area a b c * 2 := by perm; ring

lemma test_perm3 {a b c d e f: point} (H: area a c b = area f d e) : area e d f = area c a b := by perm only [area] at H; perma only [area]

lemma test_perm4 {a b c d: point} {L: line} (h: colinear b c a) (h2: triangle b d c) (h3: length d c = 1) (h4: sameside b a L) (h5: diffside d c L): angle a c b = angle b c a := by perm at h, h2, h3, h5; perm

lemma test_linperm {a b c d e f g h i: point} (H1: area a c b = 0) (H2: area c b a + area d f e = area i h g) (H3: area a c b + area f e d = 0) : area c a b + area e d f = area f d e ∧ area c a b + area e d f + area h i g = area i g h ∧ area e d f + area c a b = area h i g := by splitAll; all_goals linperm

lemma bad (a b c d : point) : angle a b c = angle a b d := sorry

lemma linperm2 (a b c d : point) : angle c b a + angle a b c = 2 * angle a b d := by
  linperm only [bad a b c d]

lemma B_or_B_of_B_B (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
    B b c d ∨ B b d c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases B_of_three_online_ne (ne_23_of_B Babc) (ne_23_of_B Babd) cd bL 
    (online_3_of_B Babc aL bL) (online_3_of_B Babd aL bL) with Bet | Bet | Bet
  left; exact Bet; exfalso; exact (not_B324_of_B123_B124 Babc Babd) Bet; right; exact Bet

lemma B_or_B_of_circ_pt (ab : a ≠ b) (aα : center_circle a α) (bα : ¬on_circle b α): 
    ∃ c, (B a c b ∨ B a b c) ∧ on_circle c α := by
  rcases pt_oncircle_of_inside_ne ab.symm $ inside_circle_of_center aα with ⟨d, Bbad, -⟩
  rcases pt_oncircle_of_inside_ne (Ne.symm $ ne_23_of_B Bbad) $ inside_circle_of_center aα with ⟨c, Bdac, cα⟩
  exact ⟨c, B_or_B_of_B_B (fun cb => bα $ by rwa [cb] at cα) Bdac $ B_symm Bbad, cα⟩ 

lemma in_circle_of_lt_lt (aα : center_circle a α) (bβ : center_circle b β) -- Look here
    (cα : on_circle c α) (dβ : on_circle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : ∃ e, on_circle e α ∧ in_circle e β := by
  by_cases bα : on_circle b α; exact ⟨b, bα, inside_circle_of_center bβ⟩
  rcases B_or_B_of_circ_pt (mt length_eq_zero_iff.mpr $ by linarith[abs_lt.mp lt_cen]) aα bα with
   ⟨e, Bet, eα⟩
  rcases Bet with Bet | Bet
  all_goals
    exact ⟨e, eα, (in_circle_iff_length_lt bβ dβ).mp $ by
     linperm[length_sum_of_B Bet, (on_circle_iff_length_eq aα cα).mpr eα, abs_lt.mp lt_cen]⟩
