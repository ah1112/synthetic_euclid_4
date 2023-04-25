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
