import sympy.Basic


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  n.fmod d ≥ 0 :=
-- proof
  Int.fmod_nonneg_of_pos n h


-- created on 2025-03-21
