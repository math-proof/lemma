import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ∀ i, |x i| = Real.sqrt (x i ^ 2) := by
-- proof
  intro i
  exact (Real.sqrt_sq_eq_abs (x i)).symm


-- created on 2021-12-21
-- updated on 2026-10-17
