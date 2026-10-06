import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : 0 ≤ x) :
-- imply
  Real.sin x ≤ x * (1 + x / Real.pi) := by
-- proof
  have h₁ : 0 ≤ x ^ 2 / Real.pi := by
    apply div_nonneg
    · exact sq_nonneg x
    · exact Real.pi_pos.le
  calc
    Real.sin x ≤ x := Real.sin_le h
    _ ≤ x + x ^ 2 / Real.pi := by linarith
    _ = x * (1 + x / Real.pi) := by ring


-- created on 2023-10-03
