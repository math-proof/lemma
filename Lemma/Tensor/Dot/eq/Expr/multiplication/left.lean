import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
  {lam : ℝ}
-- given
  (h₀ : lam ≠ 0) :
-- imply
  ∀ i, (1 / lam) * (lam * x i) = x i := by
-- proof
  intro i
  field_simp [h₀]


-- created on 2026-10-11
-- updated on 2026-10-17
