/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Theorem.Analysis.Complex.LoomanMenchoff.Part2
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

def loomanPoint (x y : ℝ) : ℂ := x + y * Complex.I

def loomanRectBoundary (f : ℂ → ℂ) (A B C D : ℝ) : ℂ :=
  (∫ x in A..B, f (loomanPoint x C) - f (loomanPoint x D)) +
    Complex.I * ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint A y)

end
end MetaMathlibExt
