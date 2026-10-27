/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2.Part6
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem fourierCoeff_eq (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (j : ℤ) :
    fourierCoeff (⇑(entry2f a ha)) j
      = 1 / (((↑(entry2w a j) : ℂ)) ^ 2) := by
  have hLift : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ)
      = AddCircle.liftIco Real.pi 0 (entry2h a) := by
    simp only [entry2f, ContinuousMap.coe_mk]
  rw [hLift, fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  have hT : ((0 : ℝ) + Real.pi - 0) = Real.pi := by ring
  have hT2 : (0 : ℝ) + Real.pi = Real.pi := zero_add _
  rw [hT, hT2]
  -- integrand equality
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hPoint : ∀ x : ℝ, fourier (-j) (↑x : AddCircle Real.pi) • entry2h a x
      = (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    intro x
    rw [smul_eq_mul]
    unfold entry2h
    rw [fourier_coe_apply]
    have hExpAdd : (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
          * Complex.exp (↑((a - 1) * x) * Complex.I))
        = Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold entry2w
      push_cast
      field_simp
      ring
    have hMul : (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
          * ((entry2A a + entry2B a * ↑x)
            * Complex.exp (↑((a - 1) * x) * Complex.I)))
        = (entry2A a + entry2B a * ↑x)
          * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
            * Complex.exp (↑((a - 1) * x) * Complex.I)) := by
      ring
    rw [hMul, hExpAdd]
  simp only [hPoint]
  rw [integral_eq_pi_div_w2 a j ha]
  rw [RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  exact one_div_mul_cancel hpi

theorem summable_fourierCoeff (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    Summable (fourierCoeff (⇑(entry2f a ha))) := by
  apply Summable.of_nat_of_neg_add_one
  · -- j = n
    have hMaj := summable_absMajorant 2 a (by omega : 2 ≤ 2)
    apply hMaj.of_norm_bounded
    intro n
    rw [fourierCoeff_eq a ha (↑n : ℤ)]
    have hcast : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hw_eq : entry2w a (↑n : ℤ) = a - (((2 * n + 1 : ℕ) : ℝ)) := by
      unfold entry2w
      rw [hcast]
    have hnorm : ‖(1 : ℂ) / (((↑(entry2w a (↑n : ℤ)) : ℂ)) ^ 2)‖
        = 1 / (|entry2w a (↑n : ℤ)| ^ 2) := by
      simp only [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hw_eq]
    unfold chapter9Entry2AbsMajorant
    have h1 : (1 : ℝ) / (|a - ↑(2 * n + 1)| ^ 2)
        = 1 / (|↑(2 * n + 1) - a| ^ 2) := by
      rw [abs_sub_comm]
    rw [h1]
    apply le_add_of_nonneg_right
    apply one_div_nonneg.mpr
    positivity
  · -- j = -(n+1)
    have hMaj := summable_absMajorant 2 a (by omega : 2 ≤ 2)
    apply hMaj.of_norm_bounded
    intro n
    have hJ : (-((↑n : ℤ) + 1) : ℤ) = (-(↑n + 1) : ℤ) := rfl
    rw [fourierCoeff_eq a ha (-((↑n : ℤ) + 1))]
    have hcast : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ))
        = -(((2 * n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hw_eq : entry2w a (-((↑n : ℤ) + 1)) = a + (((2 * n + 1 : ℕ) : ℝ)) := by
      unfold entry2w
      rw [hcast]
      ring
    have hnorm : ‖(1 : ℂ) / (((↑(entry2w a (-((↑n : ℤ) + 1))) : ℂ)) ^ 2)‖
        = 1 / (|entry2w a (-((↑n : ℤ) + 1))| ^ 2) := by
      simp only [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hw_eq]
    have hcomm : a + (((2 * n + 1 : ℕ) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) + a := by
      ring
    rw [hcomm]
    unfold chapter9Entry2AbsMajorant
    apply le_add_of_nonneg_left
    apply one_div_nonneg.mpr
    positivity

theorem hasSum_fourier (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => fourierCoeff (⇑(entry2f a ha)) j
      • fourier j (↑x : AddCircle Real.pi)) (entry2h a x) := by
  have hSum := has_pointwise_sum_fourier_series_of_summable
    (f := entry2f a ha) (summable_fourierCoeff a ha) (↑x : AddCircle Real.pi)
  have hx' : x ∈ Set.Ico (0 : ℝ) (0 + Real.pi) := by
    simpa [zero_add] using hx
  have hCoe : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ) (↑x : AddCircle Real.pi)
      = entry2h a x := by
    have h1 : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ)
        = AddCircle.liftIco Real.pi 0 (entry2h a) := by
      simp only [entry2f, ContinuousMap.coe_mk]
    rw [h1]
    exact AddCircle.liftIco_coe_apply hx'
  rw [hCoe] at hSum
  exact hSum

theorem hasSum_mul_exp (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => Complex.exp (↑((1 - a) * x) * Complex.I)
      * (fourierCoeff (⇑(entry2f a ha)) j • fourier j (↑x : AddCircle Real.pi)))
      (entry2A a + entry2B a * ↑x) := by
  have hBase := hasSum_fourier a ha x hx
  have hMul := hBase.mul_left (Complex.exp (↑((1 - a) * x) * Complex.I))
  have hRhs : Complex.exp (↑((1 - a) * x) * Complex.I) * entry2h a x
      = entry2A a + entry2B a * ↑x := by
    unfold entry2h
    have hExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
          * Complex.exp (↑((a - 1) * x) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]
      have hArg : ((↑((1 - a) * x) : ℂ) * Complex.I
            + ↑((a - 1) * x) * Complex.I) = 0 := by
        push_cast
        ring
      rw [hArg, Complex.exp_zero]
    calc Complex.exp (↑((1 - a) * x) * Complex.I)
          * ((entry2A a + entry2B a * ↑x)
            * Complex.exp (↑((a - 1) * x) * Complex.I))
        = (entry2A a + entry2B a * ↑x)
          * (Complex.exp (↑((1 - a) * x) * Complex.I)
            * Complex.exp (↑((a - 1) * x) * Complex.I)) := by ring
      _ = (entry2A a + entry2B a * ↑x) * 1 := by rw [hExp]
      _ = entry2A a + entry2B a * ↑x := by ring
  rw [hRhs] at hMul
  exact hMul

theorem hasSum_exp_div (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
      / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2))
      (entry2A a + entry2B a * ↑x) := by
  have hBase := hasSum_mul_exp a ha x hx
  apply hBase.congr_fun
  intro j
  rw [smul_eq_mul, fourierCoeff_eq a ha j, fourier_coe_apply]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
        * (1 / (((↑(entry2w a j) : ℂ)) ^ 2)
          * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi)))
      = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
        / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by
    have hArg : ((↑((1 - a) * x) : ℂ) * Complex.I
          + (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = ((↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) : ℂ) * Complex.I) := by
      push_cast
      field_simp
      ring
    have hDen : ((((↑(entry2w a j) : ℂ)) ^ 2))
        = (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by
      have hw : (↑(entry2w a j) : ℂ) = -((((2 * j + 1 : ℤ) : ℂ)) - ↑a) := by
        unfold entry2w
        push_cast
        ring
      rw [hw, neg_sq]
    have hMulExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
          * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I) := by
      rw [← Complex.exp_add, hArg]
    calc Complex.exp (↑((1 - a) * x) * Complex.I)
            * (1 / (((↑(entry2w a j) : ℂ)) ^ 2)
              * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = (Complex.exp (↑((1 - a) * x) * Complex.I)
            * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
          / (((↑(entry2w a j) : ℂ)) ^ 2) := by
          field_simp
      _ = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
          / (((↑(entry2w a j) : ℂ)) ^ 2) := by rw [hMulExp]
      _ = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
          / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by rw [hDen]
  exact hExp.symm

theorem exp_div_ofReal_re (d x : ℝ) :
    (Complex.exp (↑(d * x) * Complex.I) / (↑d : ℂ) ^ 2).re
      = Real.cos (d * x) / d ^ 2 := by
  have hdc : ((d : ℂ)) ^ 2 = ((d ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdc, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, div_eq_mul_inv,
    mul_zero, sub_zero]

theorem hasSum_cosine_re (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm 2 a x)
      ((entry2A a).re + x * (entry2B a).re) := by
  have hBase := hasSum_exp_div a ha x hx
  have hNat := hBase.nat_add_neg_add_one
  have hRe := Complex.hasSum_re hNat
  have hValEq : (entry2A a + entry2B a * (↑x : ℂ)).re
      = (entry2A a).re + x * (entry2B a).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [← hValEq]
  refine hRe.congr_fun fun n => ?_
  have hcast1 : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hcast2 : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ))
      = -(((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hd1 : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℂ)) - (↑a : ℂ)
      = ((((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a : ℝ) : ℂ) := by
    push_cast
    ring
  have hd2 : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℂ)) - (↑a : ℂ)
      = ((((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a : ℝ) : ℂ) := by
    push_cast
    ring
  rw [Complex.add_re, hd1, hd2,
    exp_div_ofReal_re _ _, exp_div_ofReal_re _ _]
  have hcos2 : (((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a) * x
      = -((((((2 * n + 1 : ℕ) : ℝ)) + a) * x)) := by
    rw [hcast2]
    ring
  have hsq2 : ((((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a)) ^ 2
      = (((((2 * n + 1 : ℕ) : ℝ)) + a)) ^ 2 := by
    rw [hcast2]
    ring
  rw [hcos2, Real.cos_neg, hsq2]
  have hcos1 : (((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a) * x
      = (((((2 * n + 1 : ℕ) : ℝ)) - a) * x) := by
    rw [hcast1]
  have hsq1 : ((((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a)) ^ 2
      = (((((2 * n + 1 : ℕ) : ℝ)) - a)) ^ 2 := by
    rw [hcast1]
  rw [hcos1, hsq1]
  simp only [chapter9Entry2CosineTerm]

end
end Entry2
end Ramanujan.Part1Ch9
end
