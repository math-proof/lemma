import sympy.functions.elementary.trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : (∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
    ∀ l : ℤ, y ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) :
-- imply
  Real.tan (x + y) = (Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y) := by
-- proof
  exact Real.tan_add' h


-- created on 2020-12-06
-- updated on 2023-06-01
