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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part4
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

theorem tanTerm_eq_chap9T (x : ℝ) (k : ℕ) :
    chapter9Entry19TanTerm x k = chap9T (Real.tan x) k := by
  rfl

theorem tsum_tan_eq_chap9T (x : ℝ) :
    (∑' k : ℕ, chapter9Entry19TanTerm x k) = ∑' k : ℕ, chap9T (Real.tan x) k :=
  rfl

theorem chap9D_eq_central {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    chap9D x = (∑' k : ℕ, chapter9Entry19CentralTerm x k)
      - (Real.pi / 2 * Real.log (2 * Real.cos x)
        + (∑' k : ℕ, chapter9Entry19TanTerm x k)) := by
  unfold chap9D
  rw [tsum_central_split_aux hx0 hx, tsum_tan_eq_chap9T]

theorem cos_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.cos x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hcos_pos := le_of_lt (cos_pos_aux hx0 hx)
  have hcos_le := Real.cos_le_one x
  constructor <;> linarith

theorem sin_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.sin x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsin_nn := sin_nonneg_aux hx0 hx
  have hsin_le := Real.sin_le_one x
  constructor <;> linarith

theorem tan_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ∈ Set.Icc (-1 : ℝ) 1 := by
  have htan_nn := tan_nonneg_aux hx0 hx
  have htan_le := tan_le_one_aux hx0 hx
  constructor <;> linarith

theorem continuousOn_S_cos :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_cos.continuousOn
    (fun x hx => cos_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.cos
      = (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k) := rfl
  rwa [hEq] at hcomp

theorem continuousOn_S_sin :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_sin.continuousOn
    (fun x hx => sin_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.sin
      = (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k) := rfl
  rwa [hEq] at hcomp

theorem continuousOn_T_tan :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    have h := Set.mem_Icc.mp hx
    constructor <;> linarith
  have htan_cont : ContinuousOn Real.tan (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuousOn_tan_Ioo.mono hsub
  have hcomp := continuousOn_chap9T_tsum_aux.comp htan_cont
    (fun x hx => tan_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun v : ℝ => ∑' k : ℕ, chap9T v k) ∘ Real.tan
      = (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k) := rfl
  rwa [hEq] at hcomp

theorem continuousOn_log_two_cos :
    ContinuousOn (fun x : ℝ => Real.log (2 * Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcos_cont : ContinuousOn (fun x : ℝ => 2 * Real.cos x)
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul Real.continuous_cos.continuousOn
  have hcomp := Real.continuousOn_log.comp hcos_cont (fun x hx => by
    have h := Set.mem_Icc.mp hx
    have hcos := cos_pos_aux h.1 h.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith)
  have hEq : Real.log ∘ (fun x : ℝ => 2 * Real.cos x)
      = (fun x : ℝ => Real.log (2 * Real.cos x)) := rfl
  rwa [hEq] at hcomp

theorem continuousOn_chap9D :
    ContinuousOn chap9D (Set.Icc 0 (Real.pi / 4)) := by
  unfold chap9D
  exact ((continuousOn_S_cos.add continuousOn_S_sin).sub
    ((continuousOn_const.mul continuousOn_log_two_cos).add continuousOn_T_tan))

theorem arcsin_sin_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arcsin (Real.sin x) = x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arcsin_sin (by linarith) (by linarith)

theorem arcsin_cos_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arcsin (Real.cos x) = Real.pi / 2 - x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have harccos : Real.arccos (Real.cos x) = x :=
    Real.arccos_cos (le_of_lt hx0) (by linarith)
  have h := Real.arcsin_eq_pi_div_two_sub_arccos (Real.cos x)
  rw [harccos] at h
  exact h

theorem arctan_tan_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arctan (Real.tan x) = x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arctan_tan (by linarith) (by linarith)

theorem hasDerivAt_chap9D {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    HasDerivAt chap9D 0 x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_mem := cos_mem_Ioo_of_mem hx0 hx
  have hsin_mem := sin_mem_Ioo_of_mem hx0 hx
  have htan_mem := tan_mem_Ioo_of_mem hx0 hx
  have hcos_pos : 0 < Real.cos x := hcos_mem.1
  have hsin_pos : 0 < Real.sin x := hsin_mem.1
  have htan_pos : 0 < Real.tan x := htan_mem.1
  have hcos_ne : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  have htan_ne : Real.tan x ≠ 0 := ne_of_gt htan_pos
  have hcos_abs := abs_cos_lt_one_of_mem hx0 hx
  have hsin_abs := abs_sin_lt_one_of_mem hx0 hx
  have htan_abs := abs_tan_lt_one_of_mem hx0 hx
  have h_arcsin_sin := arcsin_sin_eq_of_mem hx0 hx
  have h_arcsin_cos := arcsin_cos_eq_of_mem hx0 hx
  have h_arctan_tan := arctan_tan_eq_of_mem hx0 hx
  have hS1 : Real.cos x * (∑' k : ℕ, chap9Sderiv (Real.cos x) k)
      = Real.pi / 2 - x := by
    have h := mul_tsum_Sderiv_eq_arcsin hcos_abs
    rwa [h_arcsin_cos] at h
  have hS2 : Real.sin x * (∑' k : ℕ, chap9Sderiv (Real.sin x) k) = x := by
    have h := mul_tsum_Sderiv_eq_arcsin hsin_abs
    rwa [h_arcsin_sin] at h
  have hT : Real.tan x * (∑' k : ℕ, chap9Tderiv (Real.tan x) k) = x := by
    have h := mul_tsum_Tderiv_eq_arctan htan_abs
    rwa [h_arctan_tan] at h
  have hS_cos_has : HasDerivAt (fun u : ℝ => ∑' k : ℕ, chap9S u k)
      (∑' k : ℕ, chap9Sderiv (Real.cos x) k) (Real.cos x) :=
    hasDerivAt_chap9S hcos_abs
  have hS_sin_has : HasDerivAt (fun u : ℝ => ∑' k : ℕ, chap9S u k)
      (∑' k : ℕ, chap9Sderiv (Real.sin x) k) (Real.sin x) :=
    hasDerivAt_chap9S hsin_abs
  have hT_has : HasDerivAt (fun v : ℝ => ∑' k : ℕ, chap9T v k)
      (∑' k : ℕ, chap9Tderiv (Real.tan x) k) (Real.tan x) :=
    hasDerivAt_chap9T htan_abs
  have hcos_deriv := Real.hasDerivAt_cos x
  have hsin_deriv := Real.hasDerivAt_sin x
  have htan_deriv := Real.hasDerivAt_tan hcos_ne
  have hS_cos_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k)
      ((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x)) x :=
    hS_cos_has.comp x hcos_deriv
  have hS_sin_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k)
      ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)) x :=
    hS_sin_has.comp x hsin_deriv
  have hT_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k)
      ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)) x :=
    hT_has.comp x htan_deriv
  have h2cos_deriv : HasDerivAt (fun x : ℝ => 2 * Real.cos x) (2 * (-Real.sin x)) x :=
    hcos_deriv.const_mul 2
  have h2cos_ne : (2 : ℝ) * Real.cos x ≠ 0 := by
    positivity
  have hlog_deriv : HasDerivAt (fun x : ℝ => Real.log (2 * Real.cos x))
      ((2 * (-Real.sin x)) / (2 * Real.cos x)) x :=
    h2cos_deriv.log h2cos_ne
  have hlog_const : HasDerivAt (fun x : ℝ => Real.pi / 2 * Real.log (2 * Real.cos x))
      ((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x))) x :=
    hlog_deriv.const_mul (Real.pi / 2)
  have hLHS : HasDerivAt
      (fun x : ℝ => (∑' k : ℕ, chap9S (Real.cos x) k)
        + (∑' k : ℕ, chap9S (Real.sin x) k))
      (((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
        + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x))) x :=
    hS_cos_comp.add hS_sin_comp
  have hRHS : HasDerivAt
      (fun x : ℝ => (Real.pi / 2 * Real.log (2 * Real.cos x))
        + (∑' k : ℕ, chap9T (Real.tan x) k))
      (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
        + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2))) x :=
    hlog_const.add hT_comp
  have hDfun : HasDerivAt
      (fun x : ℝ => ((∑' k : ℕ, chap9S (Real.cos x) k)
        + (∑' k : ℕ, chap9S (Real.sin x) k))
        - (Real.pi / 2 * Real.log (2 * Real.cos x)
          + (∑' k : ℕ, chap9T (Real.tan x) k)))
      ((((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
        + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)))
        - (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
          + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)))) x :=
    hLHS.sub hRHS
  have hDeriv_zero : ((((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
      + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)))
      - (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
        + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)))) = 0 := by
    have hS1' : (∑' k : ℕ, chap9Sderiv (Real.cos x) k)
        = (Real.pi / 2 - x) / Real.cos x := by
      rw [eq_div_iff hcos_ne]
      linarith [hS1]
    have hS2' : (∑' k : ℕ, chap9Sderiv (Real.sin x) k) = x / Real.sin x := by
      rw [eq_div_iff hsin_ne]
      linarith [hS2]
    have hT' : (∑' k : ℕ, chap9Tderiv (Real.tan x) k) = x / Real.tan x := by
      rw [eq_div_iff htan_ne]
      linarith [hT]
    have htan_eq : Real.tan x = Real.sin x / Real.cos x :=
      Real.tan_eq_sin_div_cos x
    have hsq : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq x
    have hsc_ne : Real.sin x / Real.cos x ≠ 0 :=
      div_ne_zero hsin_ne hcos_ne
    have h2c_ne : (2 : ℝ) * Real.cos x ≠ 0 :=
      mul_ne_zero (by norm_num) hcos_ne
    rw [hS1', hS2', hT', htan_eq]
    field_simp
    have h2 : x * (Real.sin x ^ 2 + Real.cos x ^ 2) = x := by
      rw [hsq, mul_one]
    nlinarith [h2, hsq]
  rw [hDeriv_zero] at hDfun
  exact hDfun

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
