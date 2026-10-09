import sympy.Basic


@[path]
private lemma main
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  a > 0 :=
-- proof
  Nat.zero_lt_of_lt h


@[path]
private lemma transit
  {x y : ℝ}
-- given
  (hy : y ≥ 0)
  (h : x > y) :
-- imply
  x > 0 := by
-- proof
  exact lt_of_le_of_lt hy h


-- created on 2019-07-06
-- updated on 2026-09-27
