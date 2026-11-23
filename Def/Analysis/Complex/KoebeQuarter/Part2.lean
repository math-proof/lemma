/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.Complex.KoebeQuarter.Part2

@[expose] public section

/-!
# Koebe one-quarter theorem
-/


section

namespace Complex.KoebeQuarterWanted

open MeasureTheory

/-- The real-linear ellipse map `ζ ↦ ρ⁻¹ * (starRingEnd ℂ ζ) + c * ρ * ζ`. -/
noncomputable def koebeEll (ρ : ℝ) (c : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (LinearMap.mulLeft ℝ ((ρ⁻¹ : ℝ) : ℂ)).comp
    Complex.conjAe.toLinearEquiv.toLinearMap +
    LinearMap.mulLeft ℝ (c * (ρ : ℂ))

end Complex.KoebeQuarterWanted
end
