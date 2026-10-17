import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


/--
On the open interval `(0, π)`, `x + sin x` is strictly larger than `x`.
-/
@[path]
private lemma main
  {x : ℝ}
  (h₀ : 0 < x)
  (h₁ : x < Real.pi) :
-- imply
  x < x + Real.sin x := by
-- proof
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi h₀ h₁
  linarith


-- created on 2026-10-11
-- updated on 2026-10-17
