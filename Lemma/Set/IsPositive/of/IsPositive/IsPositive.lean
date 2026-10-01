import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ioi 0)
  (h₁ : y ∈ Set.Ioi 0) :
-- imply
  x * y ∈ Set.Ioi 0 := by
-- proof
  rw [Set.mem_Ioi] at *
  exact mul_pos h₀ h₁


-- created on 2022-04-03
