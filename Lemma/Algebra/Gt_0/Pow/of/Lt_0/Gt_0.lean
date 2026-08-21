import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {n : ℤ}
-- given
  (h_n : n < 0)
  (h_x : x > 0) :
-- imply
  x ^ n > 0 := by
-- proof
  have := h_n
  exact zpow_pos h_x n


-- created on 2023-04-15
-- updated on 2026-08-20
