import sympy.Basic


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.take i).prod * (s.drop i).prod := by
-- proof
  simp


-- created on 2025-06-08
