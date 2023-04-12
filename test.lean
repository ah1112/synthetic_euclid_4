lemma test_perm {a b c d e f u v w x y z: point} (h: area u v w + area x y z = 1)
  : (area a c c = area c c a) ∧ (area a b c + area e d f = area a c b + area d f e) ∧ (area a b c + area c b a = area a b c * 2) ∧ (area b a c + area c b a = area a b c * 2) ∧ (area b a c + area a b c = area a b c * 2) := by
  have := h
  constructor
  perm
  constructor
  perm 2
  constructor
  perm then ring_nf
  constructor
  perm then {perm then ring_nf}
  perm then {perm then ring_nf}