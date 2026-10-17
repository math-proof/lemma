import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import sympy.Basic
open MeasureTheory


@[path]
private lemma main :
-- imply
  ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
-- proof
  have h := integral_gaussian (1 / 2)
  have hI : (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) = ∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2) := by
    refine congrArg (integral volume) ?_
    funext x
    congr 1
    ring
  rw [hI, h]
  have : Real.pi / (1 / 2) = 2 * Real.pi := by
    ring
  rw [this]


-- created on 2026-10-11
-- updated on 2026-10-17
