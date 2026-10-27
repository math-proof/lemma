/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

theorem cos_pos_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor <;> linarith

theorem sin_nonneg_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 ≤ Real.sin x := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi hx0
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

theorem tan_nonneg_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 ≤ Real.tan x := by
  apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two hx0
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

theorem tan_le_one_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx_mem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hpi4_mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have h := Real.strictMonoOn_tan.monotoneOn hx_mem hpi4_mem hx
  rwa [Real.tan_pi_div_four] at h

theorem summable_two_div_succ_sq :
    Summable (fun k : ℕ => (2 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr one_lt_two
  have h2 : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
    have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h
    exact hshift
  have h3 := h2.mul_left (2 : ℝ)
  simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h3

theorem sq_succ_le_aux (k : ℕ) :
    ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  have hk : k + 1 ≤ 2 * k + 1 := by omega
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hk) 2

theorem Dpos_aux (k : ℕ) : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  apply pow_pos
  apply Nat.cast_pos.mpr
  omega

theorem summable_central_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Summable (chapter9Entry19CentralTerm x) := by
  have hcos := cos_pos_aux hx0 hx
  have hsin_nn := sin_nonneg_aux hx0 hx
  have hcos_le : Real.cos x ≤ 1 := Real.cos_le_one x
  have hsin_le : Real.sin x ≤ 1 := Real.sin_le_one x
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_two_div_succ_sq
  · unfold chapter9Entry19CentralTerm
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply add_nonneg <;> apply pow_nonneg
      · exact le_of_lt hcos
      · exact hsin_nn
    · apply mul_nonneg
      · apply pow_nonneg; norm_num
      · apply pow_nonneg; exact Nat.cast_nonneg _
  · have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have hS2 : Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1) ≤ 2 := by
      have c1 : Real.cos x ^ (2 * k + 1) ≤ 1 :=
        pow_le_one₀ (le_of_lt hcos) hcos_le
      have c2 : Real.sin x ^ (2 * k + 1) ≤ 1 :=
        pow_le_one₀ hsin_nn hsin_le
      linarith
    have hSD : (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
        ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have he := sq_succ_le_aux k
      have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        apply pow_pos
        apply Nat.cast_pos.mpr
        omega
      have step1 : (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
          ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hS2 (le_of_lt hD)
      have step2 : (2 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hepos he
      exact le_trans step1 step2
    have hSDnn : (0 : ℝ) ≤ (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
        ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply div_nonneg _ (le_of_lt hD)
      apply add_nonneg <;> apply pow_nonneg
      · exact le_of_lt hcos
      · exact hsin_nn
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        ((Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
          ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤ 2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    unfold chapter9Entry19CentralTerm
    rw [← div_mul_div_comm]
    exact hmul

theorem summable_tan_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Summable (chapter9Entry19TanTerm x) := by
  have htan_nn := tan_nonneg_aux hx0 hx
  have htan_le := tan_le_one_aux hx0 hx
  refine Summable.of_norm_bounded summable_two_div_succ_sq (fun k => ?_)
  have habs : |Real.tan x| ≤ 1 := by rwa [abs_of_nonneg htan_nn]
  have hD := Dpos_aux k
  have he := sq_succ_le_aux k
  have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    apply Nat.cast_pos.mpr
    omega
  have hpow : |Real.tan x| ^ (2 * k + 1) ≤ 1 :=
    pow_le_one₀ (abs_nonneg (Real.tan x)) habs
  have hle : |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    have step1 : |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hpow (le_of_lt hD)
    have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hepos he
    have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
    exact le_trans step1 (le_trans hinv h12)
  have hnorm : ‖chapter9Entry19TanTerm x k‖ =
      |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    unfold chapter9Entry19TanTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hD]
  rw [hnorm]
  exact hle

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
