import sympy.Basic
import Mathlib


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ioi 0)
  (h₁ : y ∈ Set.Iio 0) :
-- imply
  x * y ∈ Set.Iio 0 := by
-- proof
  rw [Set.mem_Ioi, Set.mem_Iio] at *
  exact mul_neg_of_pos_of_neg h₀ h₁


-- created on 2022-04-03
