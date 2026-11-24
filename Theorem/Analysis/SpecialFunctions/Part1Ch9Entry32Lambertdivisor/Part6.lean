module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part6


public section

/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem hasDerivAt_H32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt H32 (1 / (2 * mu32 z)) z := by
  have hzN : ‖z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hz0]
    exact hz1
  have hS := S32_hasDerivAt_of_norm_lt_one hzN
  have hMu := hasDerivAt_mu32 hz0 hz1
  have hH := hMu.mul hS
  have hDeriv : deriv S32 z
      = ∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1) :=
    hS.deriv
  have hODE := ode_S32_of_norm_lt_one hzN
  have hmu2 := mu32_sq hz0.le hz1.le
  have hmuN := mu32_ne_zero hz0 hz1
  have hEq : ((1 - 2 * z) / (2 * mu32 z)) * S32 z
        + mu32 z * (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))
      = 1 / (2 * mu32 z) := by
    rw [← hDeriv]
    field_simp
    rw [hmu2]
    linear_combination hODE
  have e1 : (mu32 * S32) = H32 := by
    funext y
    rfl
  rw [e1] at hH
  have e2 : ((1 - 2 * z) / (2 * mu32 z)) * S32 z
        + mu32 z * (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))
      = 1 / (2 * mu32 z) :=
    hEq
  rw [e2] at hH
  exact hH

theorem continuous_mu32 : Continuous mu32 := by
  have hinner : Continuous (fun z : ℝ => z * (1 - z)) := by continuity
  have hcomp : Continuous (Real.sqrt ∘ (fun z : ℝ => z * (1 - z))) :=
    Real.continuous_sqrt.comp hinner
  have e : (Real.sqrt ∘ (fun z : ℝ => z * (1 - z))) = mu32 := by
    funext z
    rfl
  rw [e] at hcomp
  exact hcomp

theorem continuous_A32 : Continuous A32 := by
  have hcomp : Continuous (Real.arcsin ∘ Real.sqrt) :=
    Real.continuous_arcsin.comp Real.continuous_sqrt
  have e : (Real.arcsin ∘ Real.sqrt) = A32 := by
    funext z
    rfl
  rw [e] at hcomp
  exact hcomp

theorem continuousAt_S32_zero : ContinuousAt S32 0 := by
  have h0 : ‖(0:ℝ)‖ < 1 := by norm_num
  exact (S32_hasDerivAt_of_norm_lt_one h0).continuousAt

theorem H32_zero : H32 0 = 0 := by
  unfold H32
  rw [mu32_zero, S32_zero]
  ring

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
