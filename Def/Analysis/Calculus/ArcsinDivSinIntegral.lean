/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.BigOperators.Fin
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

def adsHalfArcsinSinSq (x : ℝ) : ℝ :=
  Real.arcsin (Real.sin x ^ 2) / 2

def adsHalfArcsinSinSqDeriv (x : ℝ) : ℝ :=
  Real.sin x / Real.sqrt (1 + Real.sin x ^ 2)

def adsRawIntegrand (x : ℝ) : ℝ :=
  2 * x * Real.sqrt (1 + Real.sin (2 * x)) / Real.sin (2 * x)

def adsJIntegrand (x : ℝ) : ℝ :=
  x * (1 / Real.cos x + 1 / Real.sin x)

def adsLogTanIntegral (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, Real.log (Real.tan x)

def adsLogTanHalf (x : ℝ) : ℝ :=
  Real.log (Real.tan (x / 2))

def adsLogTanShift (x : ℝ) : ℝ :=
  Real.log (Real.tan (x / 2 + Real.pi / 4))

def adsLogTanProducts (x : ℝ) : ℝ :=
  x * adsLogTanHalf x + x * adsLogTanShift x

end
end Real.Calculus.ArcsinDivSinIntegral
