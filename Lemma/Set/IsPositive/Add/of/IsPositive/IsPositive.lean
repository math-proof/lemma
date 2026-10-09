import sympy.Basic
import Mathlib


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ioi 0)
  (h₁ : y ∈ Set.Ioi 0) :
-- imply
  x + y ∈ Set.Ioi 0 := by
-- proof
  rw [Set.mem_Ioi] at *
  exact add_pos h₀ h₁


-- created on 2023-05-03
