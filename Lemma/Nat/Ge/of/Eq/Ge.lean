import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b : ℝ}
-- given
  (h₀ : a = x)
  (h₁ : x ≥ b) :
-- imply
  a ≥ b := by
-- proof
  rw [h₀]
  exact h₁


@[main]
private lemma subst
  {y b x t k : ℝ}
-- given
  (hk : k > 0)
  (h₀ : y = x * k + b)
  (h₁ : x ≥ t) :
-- imply
  y ≥ t * k + b := by
-- proof
  nlinarith


-- created on 2026-09-27
