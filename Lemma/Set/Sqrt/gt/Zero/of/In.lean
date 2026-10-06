import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioo (-1) 1) :
-- imply
  Real.sqrt (1 - x ^ 2) > 0 := by
-- proof
  obtain ⟨h₁, h₂⟩ := h
  apply Real.sqrt_pos.mpr
  have h₃ : (1 - x) * (1 + x) > 0 := mul_pos (sub_pos.mpr h₂) (by linarith)
  nlinarith [h₃]


-- created on 2020-11-26
