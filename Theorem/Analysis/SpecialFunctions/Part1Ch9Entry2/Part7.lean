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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2.Part7
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

theorem inv_one_add_E_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    ((1 + entry2E a)⁻¹).re = 1 / 2 := by
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hre : (1 + entry2E a).re = 1 + Real.cos (Real.pi * a) := by
    simp only [Complex.add_re, Complex.one_re, entry2E, Complex.exp_ofReal_mul_I_re]
  have him : (1 + entry2E a).im = Real.sin (Real.pi * a) := by
    simp only [Complex.add_im, Complex.one_im, entry2E, Complex.exp_ofReal_mul_I_im,
      zero_add]
  have hns : (1 + entry2E a).normSq = 2 * (1 + entry2E a).re := by
    rw [Complex.normSq_apply, him, hre]
    have hcs : Real.cos (Real.pi * a) ^ 2 + Real.sin (Real.pi * a) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    linear_combination hcs
  have hre_ne : (1 + entry2E a).re ≠ 0 := by
    intro h0
    apply hNe
    have h00 : (1 + entry2E a).normSq = 0 := by rw [hns, h0, mul_zero]
    exact Complex.normSq_eq_zero.mp h00
  have h2 : 2 * (1 + entry2E a).re ≠ 0 := mul_ne_zero (by norm_num) hre_ne
  rw [Complex.inv_re, hns, div_eq_div_iff h2 (by norm_num)]
  ring

theorem entry2B_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (entry2B a).re = -Real.pi / 2 := by
  have h := inv_one_add_E_re a ha
  unfold entry2B
  rw [div_eq_mul_inv, Complex.mul_re]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero]
  rw [h]
  ring

theorem cosineTerm_zero_eq (r : ℕ) (a : ℝ) (k : ℕ) :
    chapter9Entry2CosineTerm r a 0 k = chapter9Entry2ConstantTerm r a k := by
  unfold chapter9Entry2CosineTerm chapter9Entry2ConstantTerm
  simp only [mul_zero, Real.cos_zero]

theorem sineTerm_zero_eq (r : ℕ) (a : ℝ) (k : ℕ) :
    chapter9Entry2SineTerm r a 0 k = 0 := by
  unfold chapter9Entry2SineTerm
  simp only [mul_zero, Real.sin_zero, zero_div, add_zero]

theorem summable_cosineTerm_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) :
    Summable (fun k => chapter9Entry2CosineTerm r a 0 k) := by
  have hfun : (fun k => chapter9Entry2CosineTerm r a 0 k)
      = chapter9Entry2ConstantTerm r a := by
    funext k
    exact cosineTerm_zero_eq r a k
  rw [hfun]
  exact summable_chapter9Entry2ConstantTerm r a hr

theorem entry2A_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (entry2A a).re = chapter9Entry2Constant 2 a := by
  have hx0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos⟩
  have hBase := hasSum_cosine_re a ha 0 hx0
  rw [zero_mul, add_zero] at hBase
  have hC : HasSum (chapter9Entry2ConstantTerm 2 a)
      (chapter9Entry2Constant 2 a) :=
    (summable_chapter9Entry2ConstantTerm 2 a (by omega)).hasSum
  have hfun : chapter9Entry2CosineTerm 2 a 0
      = chapter9Entry2ConstantTerm 2 a := by
    funext k
    exact cosineTerm_zero_eq 2 a k
  rw [hfun] at hBase
  exact hBase.unique hC

theorem Pcos_two (a x : ℝ) :
    entry2Pcos 2 a x = chapter9Entry2Constant 2 a - Real.pi * x / 2 := by
  have h22 : (2 / 2 : ℕ) = 1 := by omega
  have h21 : (2 - 1 : ℕ) = 1 := rfl
  have hf0 : (0 : ℕ).factorial = 1 := rfl
  have hf1 : (1 : ℕ).factorial = 1 := rfl
  unfold entry2Pcos entry2CosSummand entry2CosPi
  rw [h22, h21, Finset.sum_range_one]
  simp only [mul_zero, Nat.sub_zero, pow_zero, pow_one, hf0, hf1, Nat.cast_one,
    one_mul, mul_one, div_one]
  ring

theorem hasSum_Q2 (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm 2 a x) (entry2Pcos 2 a x) := by
  have hBase := hasSum_cosine_re a ha x hx
  have hval : (entry2A a).re + x * (entry2B a).re = entry2Pcos 2 a x := by
    rw [entry2A_re a ha, entry2B_re a ha, Pcos_two a x]
    ring
  rw [hval] at hBase
  exact hBase

end
end Entry2
end Ramanujan.Part1Ch9
end
