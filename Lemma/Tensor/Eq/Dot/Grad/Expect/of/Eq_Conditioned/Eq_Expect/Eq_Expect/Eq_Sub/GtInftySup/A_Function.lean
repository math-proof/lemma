import sympy.Basic


@[path]
private lemma main
  {γ r V Q : ℝ}
-- given
  (h₀ : γ < 1)
  (h₁ : Q = (1 - γ) * r + γ * V) :
-- imply
  Q - γ * V = (1 - γ) * r ∧ 0 < 1 - γ := by
-- proof
  constructor
  ·
    rw [h₁]
    ring
  ·
    linarith [h₀]


-- created on 2023-04-13
-- updated on 2026-10-17
