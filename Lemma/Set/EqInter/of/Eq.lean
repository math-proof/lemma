import sympy.Basic


@[main]
private lemma main
  {A B S : Set α}
-- given
  (h : A = B) :
-- imply
  A ∩ S = B ∩ S := by
-- proof
  rw [h]


-- created on 2026-09-27
