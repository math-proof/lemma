import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (_h₀ : 0 ≤ y)
  (h₁ : y ^ 2 = x) :
-- imply
  0 ≤ x := by
-- proof
  rw [← h₁]
  nlinarith


-- created on 2023-06-20
-- updated on 2026-10-17
