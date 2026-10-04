import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 :=
-- proof
  Real.cos_two_mul' x


-- created on 2023-10-03
