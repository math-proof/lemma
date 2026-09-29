import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (ha : a ≥ 0) :
-- imply
  x ^ 2 ≤ a ↔ x ∈ Set.Icc (-√a) √a := by
-- proof
  constructor
  · intro h
    have := Real.abs_le_sqrt h
    exact ⟨(abs_le.mp this).1, (abs_le.mp this).2⟩
  · intro h
    have hs := Real.sq_sqrt ha
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (by linarith [h.1] : 0 ≤ √a + x)]


-- created on 2026-09-27
