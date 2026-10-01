import sympy.Basic


@[main]
private lemma main
  {x m M : ℝ}
-- given
  (h₀ : x ≥ m)
  (h₁ : x ≤ M) :
-- imply
  x * x ≤ max (m * m) (M * M) := by
-- proof
  rcases le_total 0 x with hx | hx
  ·
    exact le_max_of_le_right (by nlinarith)
  ·
    exact le_max_of_le_left (by nlinarith)


-- created on 2026-09-27
