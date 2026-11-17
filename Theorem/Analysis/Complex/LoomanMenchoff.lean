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

/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/

public section


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

/-- Combine derivatives of the real and imaginary parts of a complex-valued real path. -/
theorem hasDerivAt_complex_of_re_im {g : ℝ → ℂ} {a b t : ℝ}
    (hre : HasDerivAt (fun x ↦ (g x).re) a t)
    (him : HasDerivAt (fun x ↦ (g x).im) b t) :
    HasDerivAt g (a + b * Complex.I) t := by
  convert hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I) using 1
  · ext x
    exact (Complex.re_add_im (g x)).symm

end
end MetaMathlibExt
