import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
  {lam : ℝ} :
-- imply
  ∀ i, (x i + lam) + (-lam) = x i := by
-- proof
  intro i
  ring


-- created on 2026-10-11
-- updated on 2026-10-17
