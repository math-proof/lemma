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
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part5


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

theorem mu32_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < mu32 z := by
  unfold mu32
  apply Real.sqrt_pos.mpr
  have h1 : (0:ℝ) < 1 - z := by linarith
  exact mul_pos hz0 h1

theorem mu32_ne_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    mu32 z ≠ 0 :=
  ne_of_gt (mu32_pos hz0 hz1)

theorem mu32_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    mu32 z ^ 2 = z * (1 - z) := by
  unfold mu32
  have hnn : (0:ℝ) ≤ z * (1 - z) := by
    have h1 : (0:ℝ) ≤ 1 - z := by linarith
    exact mul_nonneg hz0 h1
  rw [Real.sq_sqrt hnn]

theorem mu32_zero : mu32 0 = 0 := by
  unfold mu32
  simp

theorem A32_zero : A32 0 = 0 := by
  unfold A32
  simp [Real.arcsin_zero]

theorem hasDerivAt_mu32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt mu32 ((1 - 2 * z) / (2 * mu32 z)) z := by
  have hg : HasDerivAt (fun w : ℝ => w * (1 - w)) (1 - 2 * z) z := by
    have h1 : HasDerivAt (fun w : ℝ => w) 1 z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun w : ℝ => (1:ℝ) - w) (-1) z :=
      HasDerivAt.const_sub 1 (hasDerivAt_id' z)
    have hmul := h1.mul h2
    have hval : (1:ℝ) * (1 - z) + z * (-1) = 1 - 2 * z := by ring
    rw [hval] at hmul
    exact hmul
  have hne : z * (1 - z) ≠ 0 := by
    have h1 : (0:ℝ) < 1 - z := by linarith
    exact ne_of_gt (mul_pos hz0 h1)
  have hsqrt := hg.sqrt hne
  have e1 : (fun y : ℝ => √(y * (1 - y))) = mu32 := by
    funext y
    rfl
  have e2 : (1 - 2 * z) / (2 * √(z * (1 - z)))
      = (1 - 2 * z) / (2 * mu32 z) := by
    rfl
  rw [e1, e2] at hsqrt
  exact hsqrt

theorem hasDerivAt_A32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt A32 (1 / (2 * mu32 z)) z := by
  have hzN : z ≠ 0 := ne_of_gt hz0
  have hsqrt : HasDerivAt (fun w : ℝ => √(w)) (1 / (2 * √z)) z :=
    Real.hasDerivAt_sqrt hzN
  have hsz0 : (0:ℝ) < √z := Real.sqrt_pos.mpr hz0
  have hsz1 : √z < 1 := by
    have h : √z < √(1:ℝ) :=
      (Real.sqrt_lt_sqrt_iff hz0.le).mpr hz1
    rwa [Real.sqrt_one] at h
  have h1 : √z ≠ -1 := by
    have := ne_of_gt hsz0
    linarith [this]
  have h2 : √z ≠ 1 := ne_of_lt hsz1
  have harcsin : HasDerivAt Real.arcsin (1 / √(1 - (√z) ^ 2)) (√z) :=
    Real.hasDerivAt_arcsin h1 h2
  have hcomp := harcsin.comp z hsqrt
  have e1 : (Real.arcsin ∘ Real.sqrt) = A32 := by
    funext y
    rfl
  rw [e1] at hcomp
  have hsq : (√z) ^ 2 = z := Real.sq_sqrt hz0.le
  have hmu : mu32 z = √z * √(1 - z) := by
    unfold mu32
    rw [Real.sqrt_mul hz0.le]
  have hval : (1 / √(1 - (√z) ^ 2)) * (1 / (2 * √z))
      = 1 / (2 * mu32 z) := by
    rw [hsq, hmu]
    have hz1pos : (0:ℝ) < 1 - z := by linarith
    have hszne : √z ≠ 0 := ne_of_gt hsz0
    have h1zne : √(1 - z) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hz1pos)
    field_simp
  rw [hval] at hcomp
  exact hcomp

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
