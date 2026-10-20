import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


/--
Cubic lower bound for the sine, under the same hypothesis `0 ≤ x` as Redheffer's rational bound
`sin x ≥ x (π² - x²) / (π² + x²)`.
-/
@[path]
private lemma main
  {x : ℝ}
  (h₀ : 0 ≤ x) :
-- imply
  x - x ^ 3 / 6 ≤ Real.sin x := by
-- proof
  apply Real.sin_ge_sub_cube h₀


-- created on 2023-10-03
-- updated on 2026-10-17
