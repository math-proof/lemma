import sympy.Basic
import Mathlib


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Iio 0)
  (h₁ : y ∈ Set.Iio 0) :
-- imply
  x * y ∈ Set.Ioi 0 := by
-- proof
  rw [Set.mem_Iio, Set.mem_Ioi] at *
  exact mul_pos_of_neg_of_neg h₀ h₁


-- created on 2022-04-03
