import sympy.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y) :
-- imply
  (x : ℤ) - (y : ℤ) ≥ 0 := by
-- proof
  linarith


-- created on 2025-10-16
