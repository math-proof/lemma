/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Order.LeftRightNhds
public import Theorem.Analysis.Complex.LoomanMenchoff.Part4

@[expose] public section

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

def loomanHolomorphicNeighborhood (s : Set ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ t, IsOpen t ∧ z ∈ t ∧ t ⊆ s ∧ DifferentiableOn ℂ f t}

end
end MetaMathlibExt
