import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : a ∈ Set.Ioi 0)
  (h₁ : b ∈ Set.Iio 0) :
-- imply
  a * b ∈ Set.Iio 0 := by
-- proof
  rw [Set.mem_Ioi] at h₀
  rw [Set.mem_Iio] at h₁
  exact Set.mem_Iio.mpr (mul_neg_of_pos_of_neg h₀ h₁)


-- created on 2022-04-03
-- updated on 2026-10-17
