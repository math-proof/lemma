import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : 0 < a)
  (h₁ : ∃ x : ℝ, a * x ^ 2 + b * x + c < 0) :
-- imply
  b ^ 2 - 4 * a * c > 0 := by
-- proof
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := h₁
  have heq : 4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
    ring
  have h4 : 0 < 4 * a := by positivity
  nlinarith [sq_nonneg (2 * a * x + b)]


-- created on 2022-04-03
-- updated on 2026-10-17
