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
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part8


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

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem auxZ_normSq (r x : ℝ) : Complex.normSq (auxZ r x) = r ^ 2 := by
  unfold auxZ
  rw [Complex.normSq_apply]
  have h : Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  calc (r * Real.cos (2 * x)) * (r * Real.cos (2 * x)) +
        (r * Real.sin (2 * x)) * (r * Real.sin (2 * x))
      = r ^ 2 * (Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [h]
    _ = r ^ 2 := by ring

theorem auxZ_norm_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ‖auxZ r x‖ < 1 := by
  have hsq : ‖auxZ r x‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, auxZ_normSq]
    nlinarith [hr0, hr1, sq_nonneg r]
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hsq

theorem auxZ_pow_re_im (r x : ℝ) (k : ℕ) :
    ((auxZ r x) ^ k).re = r ^ k * Real.cos ((k : ℝ) * (2 * x)) ∧
      ((auxZ r x) ^ k).im = r ^ k * Real.sin ((k : ℝ) * (2 * x)) := by
  induction k with
  | zero =>
    simp [auxZ, pow_zero]
  | succ k ih =>
    have hz_re : (auxZ r x).re = r * Real.cos (2 * x) := rfl
    have hz_im : (auxZ r x).im = r * Real.sin (2 * x) := rfl
    have hpow : (auxZ r x) ^ (k + 1) = (auxZ r x) ^ k * auxZ r x := pow_succ _ _
    have hcast : (((k + 1 : ℕ)) : ℝ) * (2 * x) = (k : ℝ) * (2 * x) + 2 * x := by
      push_cast
      ring
    rw [hpow, Complex.mul_re, Complex.mul_im, ih.1, ih.2, hz_re, hz_im, hcast,
      Real.cos_add, Real.sin_add]
    have hpow_succ : r ^ (k + 1) = r ^ k * r := pow_succ _ _
    rw [hpow_succ]
    constructor <;> ring

theorem auxZ_one_sub_normSq (r x : ℝ) :
    Complex.normSq (1 - auxZ r x) = (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 := by
  have hre : (1 - auxZ r x).re = 1 - r * Real.cos (2 * x) := by
    simp [auxZ]
  have him : (1 - auxZ r x).im = -(r * Real.sin (2 * x)) := by
    simp [auxZ]
  have hcos2 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    have h1 := Real.cos_two_mul x
    have h2 := Real.sin_sq_add_cos_sq x
    linarith
  have htrig : Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [Complex.normSq_apply, hre, him]
  linear_combination r ^ 2 * htrig + (-2 * r) * hcos2

theorem auxAr_deriv_eq_log {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    (∑' j : ℕ, auxAr_deriv_term r x j) =
      -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by
  set z : ℂ := auxZ r x with hzdef
  have hz : ‖z‖ < 1 := auxZ_norm_lt_one hr0 hr1 x
  have hcomplex := Complex.hasSum_taylorSeries_neg_log' hz
  have hre := Complex.hasSum_re hcomplex
  have hterm_eq : ∀ j : ℕ,
      (((z ^ (j + 1) / ((j : ℂ) + 1))).re) =
        r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
          ((((j + 1 : ℕ)) : ℝ)) := by
    intro j
    have hcast1 : ((j : ℂ) + 1) = ((((j + 1 : ℕ)) : ℂ)) := by
      rw [Nat.cast_add, Nat.cast_one]
    have hcast2 : ((((j + 1 : ℕ)) : ℂ)) = (((((j + 1 : ℕ)) : ℝ)) : ℂ) :=
      (Complex.ofReal_natCast _).symm
    rw [hcast1, hcast2, Complex.div_ofReal_re]
    have hpow := (auxZ_pow_re_im r x (j + 1)).1
    rw [hpow]
    have hang : ((((j + 1 : ℕ)) : ℝ)) * (2 * x) =
        2 * ((((j + 1 : ℕ)) : ℝ)) * x := by ring
    rw [hang]
  have htsum_re := hre.tsum_eq
  have htsum_real : (∑' j : ℕ, r ^ (j + 1) *
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
      (-Complex.log (1 - z)).re := by
    have hcongr : (fun j : ℕ => r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
        (fun j : ℕ => ((z ^ (j + 1) / ((j : ℂ) + 1))).re) := by
      funext j
      exact (hterm_eq j).symm
    rw [hcongr]
    exact htsum_re
  have hderiv_congr : (fun j : ℕ => auxAr_deriv_term r x j) =
      (fun j : ℕ => 2 * (r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ)))) := by
    funext j
    unfold auxAr_deriv_term
    ring
  have htsum_deriv : (∑' j : ℕ, auxAr_deriv_term r x j) =
      2 * (∑' j : ℕ, r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) := by
    rw [hderiv_congr, tsum_mul_left]
  rw [htsum_deriv, htsum_real]
  have hre_neg : (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
    rw [Complex.neg_re, Complex.log_re]
  rw [hre_neg]
  have hlog : Real.log (‖1 - z‖ ^ 2) = 2 * Real.log ‖1 - z‖ := Real.log_pow _ _
  have hnorm : ‖1 - z‖ ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 := by
    rw [Complex.sq_norm, auxZ_one_sub_normSq]
  calc 2 * -Real.log ‖1 - z‖ = -Real.log (‖1 - z‖ ^ 2) := by
        rw [hlog]
        ring
    _ = -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by rw [hnorm]

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
