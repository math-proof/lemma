import sympy.Basic
import Mathlib


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Iio 0)
  (h₁ : y ∈ Set.Iio 0) :
-- imply
  x + y ∈ Set.Iio 0 := by
-- proof
  rw [Set.mem_Iio] at *
  exact add_neg h₀ h₁


-- created on 2023-05-03
