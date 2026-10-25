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
import Theorem.Analysis.Calculus.ArcsinDivSinIntegral
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

def adsSr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def adsDr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    ((2 * k + 1 : ℕ) : ℝ)

def adsDrClosed (r x : ℝ) : ℝ :=
  Real.log ((1 + 2 * r * Real.cos (2 * x) + r ^ 2) /
    (1 - 2 * r * Real.cos (2 * x) + r ^ 2)) / 2

def adsRho (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 1)

end
end Real.Calculus.ArcsinDivSinIntegral
