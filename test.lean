import SyntheticEuclid4.tactics
open incidence_geometry
variable [i: incidence_geometry]

-- TODO: unify both cases
lemma test_perm1 {a b : point} : (area a b b = area b b a):= by
  perm'

lemma test_perm2 {a b c d e f: point} :
 (area a b c + area e d f = area a c b + area d f e) := by
  perm

lemma test_perm3 {a b c d e f: point} :
 (area a b c + area e d f = area a c b + area d f e) := by
  perm

-- TODO: take care of brackets
lemma test_perm4 {a b c: point} :
 (area b a c + area c b a = area a b c * 2) := by
  {
    conv =>
      lhs
      args
      all_goals try {perm_nf}
    
    conv =>
      rhs
      args
      all_goals try {perm_nf}
    ring
  }

lemma test_perm5 {a b c d e f: point} (H: area a c b = area f d e)
  : (area c a b = area e d f) := by
  perm' at H
  perm'
  exact H

lemma test_perm6 {a b c d e f: point} (H: area a c b = 0)
  : (area c a b + area e d f = area f d e) := by
  perm' at H
  sorry

lemma test_perm7 {a b c d e f g h i: point} (H: area a c b + area f e d = 0)
  : (area c a b + area e d f + area h i g = area i g h) := by
  sorry

lemma test_perm8 {a b c d e f g h i: point} (H: area c b a + area d f e = area i h g)
  : (area e d f + area c a b = area h i g) := by
  sorry