import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A = B)
  (S : Set α) :
-- imply
  A \ S = B \ S := by
-- proof
  rw[h]


-- created on 2025-10-01
