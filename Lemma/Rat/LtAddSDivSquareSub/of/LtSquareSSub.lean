import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x₀ x₁ y₀ y₁ y₂ : ℝ}
-- given
  (h : (y₂ - (x₀ + x₁) / 2) ^ 2 < (y₂ * 2 / 3 - (y₀ + y₁) / 3) ^ 2) :
-- imply
  ((x₀ - x₁) ^ 2 + (x₁ - y₂) ^ 2 + (y₂ - x₀) ^ 2) / 3 + (y₀ - y₁) ^ 2 / 2 <
      (x₀ - x₁) ^ 2 / 2 + ((y₀ - y₁) ^ 2 + (y₁ - y₂) ^ 2 + (y₂ - y₀) ^ 2) / 3 := by
-- proof
  nlinarith [sq_nonneg (y₂ - (x₀ + x₁) / 2)]


-- created on 2020-01-02
