import sympy.Basic
import Mathlib


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Iic 0)
  (h₁ : y ∈ Set.Iic 0) :
-- imply
  x + y ∈ Set.Iic 0 := by
-- proof
  rw [Set.mem_Iic] at *
  exact add_nonpos h₀ h₁


-- created on 2023-05-03
