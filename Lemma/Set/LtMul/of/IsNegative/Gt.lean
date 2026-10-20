import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : x ∈ Set.Iio 0)
  (h₁ : a > b) :
-- imply
  a * x < b * x := by
-- proof
  rw [Set.mem_Iio] at h₀
  exact mul_lt_mul_of_neg_right h₁ h₀


-- created on 2023-10-15
-- updated on 2026-10-17
