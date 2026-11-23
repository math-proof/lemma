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
public import Theorem.Analysis.Calculus.ArcsinDivSinIntegral.Part2

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

def adsSineTerm (x : ℝ) (k : ℕ) : ℝ :=
  Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def adsSineSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, adsSineTerm x k

end
end Real.Calculus.ArcsinDivSinIntegral
