/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SumOverResidueClass
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Algebra.BigOperators.Fin
public import Theorem.Analysis.Calculus.ArcsinDivSinIntegral.Part3

@[expose] public section

/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

def adsResidueSum (j : ℕ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (((8 * n + j : ℕ) : ℝ) ^ 2)

end
end Real.Calculus.ArcsinDivSinIntegral
