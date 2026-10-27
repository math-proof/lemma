/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part9
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

theorem Phi32_zero : Phi32 0 = 0 := by
  unfold Phi32
  rw [s32_of_t_zero, F32_zero, G32_zero]
  ring

theorem hasDerivAt_Phi32_of_ne {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    HasDerivAt Phi32 0 t := by
  have hs : ‖s32_of_t t‖ < 1 := abs_s32_of_t_lt_one ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hDne : (1:ℝ) + t ^ 2 ≠ 0 := ne_of_gt hDpos
  have hs0 : s32_of_t t ≠ 0 := by
    unfold s32_of_t
    apply div_ne_zero _ hDne
    exact mul_ne_zero (by norm_num) ht0
  have hFtsum := F32_hasDerivAt_of_norm_lt_one hs
  have eF : (∑' k : ℕ, aCoeff32 k * (s32_of_t t) ^ (2 * k))
      = S32 ((s32_of_t t) ^ 2) := by
    have e : (fun k : ℕ => aCoeff32 k * (s32_of_t t) ^ (2 * k))
        = fun k : ℕ => aCoeff32 k * ((s32_of_t t) ^ 2) ^ k := by
      funext k
      rw [← pow_mul]
    rw [e]
    rfl
  rw [eF] at hFtsum
  have hGtsum := G32_hasDerivAt_of_norm_lt_one ht
  have eG : (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ))
      = Real.arctan t / t :=
    G32_deriv_eq_arctan_div ht ht0
  rw [eG] at hGtsum
  have hsDeriv := hasDerivAt_s32_of_t t
  have hComp := hFtsum.comp t hsDeriv
  have h2G := hGtsum.const_mul (2:ℝ)
  have hSub := hComp.sub h2G
  have ePhi : ((F32 ∘ s32_of_t) - (fun w : ℝ => 2 * G32 w)) = Phi32 := by
    funext w
    unfold Phi32
    rfl
  rw [ePhi] at hSub
  have hSval := S32_sq_eq hs hs0
  have hArcsin := arcsin_s32_eq ht
  have hSqrt := sqrt_one_sub_s32_sq ht
  have hsDef : s32_of_t t = 2 * t / (1 + t ^ 2) := rfl
  have hNpos : (0:ℝ) < 1 - t ^ 2 := by
    have habs : |t| < 1 := by
      rw [← Real.norm_eq_abs]
      exact ht
    have hmem := abs_lt.mp habs
    have hsq : t ^ 2 < 1 := by
      have hsq2 : t ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
      simpa using hsq2
    linarith [hsq]
  have hNne : (1:ℝ) - t ^ 2 ≠ 0 := ne_of_gt hNpos
  have hEq : S32 ((s32_of_t t) ^ 2)
        * (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
        - 2 * (Real.arctan t / t) = 0 := by
    rw [hSval, hArcsin, hSqrt, hsDef]
    field_simp
    ring
  have eDeriv : S32 ((s32_of_t t) ^ 2)
        * (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
        - 2 * (Real.arctan t / t) = 0 :=
    hEq
  rw [eDeriv] at hSub
  exact hSub

theorem hasDerivAt_Phi32_zero' : HasDerivAt Phi32 0 0 := by
  have ht : ‖(0:ℝ)‖ < 1 := by norm_num
  have hs : ‖s32_of_t 0‖ < 1 := by
    rw [s32_of_t_zero]
    exact ht
  have hFtsum := F32_hasDerivAt_of_norm_lt_one hs
  have eF : (∑' k : ℕ, aCoeff32 k * (s32_of_t 0) ^ (2 * k)) = 1 := by
    rw [s32_of_t_zero]
    have hsingle : HasSum (fun k : ℕ => aCoeff32 k * (0:ℝ) ^ (2 * k)) 1 := by
      have h0 : aCoeff32 0 * (0:ℝ) ^ (2 * 0) = 1 := by
        rw [aCoeff32_zero]
        norm_num
      have h00 : ∀ b : ℕ, b ≠ 0 → aCoeff32 b * (0:ℝ) ^ (2 * b) = 0 := by
        intro b hb
        have hz : (0:ℝ) ^ (2 * b) = 0 := zero_pow (by omega)
        rw [hz]
        ring
      have hS := hasSum_single (0 : ℕ) h00
      rw [h0] at hS
      exact hS
    exact hsingle.tsum_eq
  rw [eF] at hFtsum
  have hGtsum := G32_hasDerivAt_of_norm_lt_one ht
  have eG : (∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) = 1 :=
    G32_deriv_zero
  rw [eG] at hGtsum
  have hsDeriv := hasDerivAt_s32_of_t 0
  have hsVal : (2:ℝ) * (1 - (0:ℝ) ^ 2) / (1 + (0:ℝ) ^ 2) ^ 2 = 2 := by
    norm_num
  rw [hsVal] at hsDeriv
  have hComp := hFtsum.comp 0 hsDeriv
  have h2G := hGtsum.const_mul (2:ℝ)
  have hSub := hComp.sub h2G
  have ePhi : ((F32 ∘ s32_of_t) - (fun w : ℝ => 2 * G32 w)) = Phi32 := by
    funext w
    unfold Phi32
    rfl
  rw [ePhi] at hSub
  have eDeriv : (1:ℝ) * 2 - 2 * (1:ℝ) = (0:ℝ) := by ring
  have hEq : (1:ℝ) * 2 - 2 * (1:ℝ) = (0:ℝ) := eDeriv
  rw [hEq] at hSub
  exact hSub

theorem hasDerivAt_Phi32 {t : ℝ} (ht : ‖t‖ < 1) :
    HasDerivAt Phi32 0 t := by
  by_cases ht0 : t = 0
  · subst ht0
    exact hasDerivAt_Phi32_zero'
  · exact hasDerivAt_Phi32_of_ne ht ht0

theorem Phi32_eq_zero_of_mem {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Phi32 t = 0 := by
  have hopen : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-1 : ℝ) 1) := isPreconnected_Ioo
  have hf : DifferentiableOn ℝ Phi32 (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have habs : ‖x‖ < 1 := by
      have hmem := Set.mem_Ioo.mp hx
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hmem.1, hmem.2]
    have hHas := hasDerivAt_Phi32 habs
    exact hHas.differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun _ : ℝ => (0:ℝ)) (Set.Ioo (-1 : ℝ) 1) :=
    (differentiable_const (0:ℝ)).differentiableOn
  have hf' : Set.EqOn (deriv Phi32) (deriv (fun _ : ℝ => (0:ℝ)))
      (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have habs : ‖x‖ < 1 := by
      have hmem := Set.mem_Ioo.mp hx
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hmem.1, hmem.2]
    have hHas := hasDerivAt_Phi32 habs
    rw [hHas.deriv]
    simp
  have hx0 : (0:ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hfgx : Phi32 0 = (fun _ : ℝ => (0:ℝ)) 0 := Phi32_zero
  have hEq := hopen.eqOn_of_deriv_eq hpre hf hg hf' hx0 hfgx
  have h := hEq ht
  simpa using h

theorem F32_s32_eq {t : ℝ} (ht : ‖t‖ < 1) :
    F32 (s32_of_t t) = 2 * G32 t := by
  have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    have habs : |t| < 1 := by
      rw [← Real.norm_eq_abs]
      exact ht
    rw [abs_lt] at habs
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hPhi := Phi32_eq_zero_of_mem hmem
  unfold Phi32 at hPhi
  linarith [hPhi]

theorem tan_abs_lt_one_of_abs_lt {x : ℝ} (hx : |x| < Real.pi / 4) :
    ‖Real.tan x‖ < 1 := by
  have h1 : -(Real.pi / 4) < x := by
    have := abs_lt.mp hx
    linarith [this.1]
  have h2 : x < Real.pi / 4 := (abs_lt.mp hx).2
  have hmem1 : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmemx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith [h1, h2])
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmono := Real.strictMonoOn_tan
  have hlt1 : Real.tan (-(Real.pi / 4)) < Real.tan x :=
    hmono hmem1 hmemx h1
  have hlt2 : Real.tan x < Real.tan (Real.pi / 4) :=
    hmono hmemx hmem2 h2
  rw [Real.tan_pi_div_four] at hlt2
  have hneg : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  rw [hneg] at hlt1
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hlt1, hlt2]

theorem sin_two_eq_s32_of_tan {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    Real.sin (2 * x) = s32_of_t (Real.tan x) := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (cos32_pos x hx)
  have htan : Real.tan x = Real.sin x / Real.cos x :=
    Real.tan_eq_sin_div_cos x
  have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    have h := Real.sin_two_mul x
    linarith [h]
  have hsq : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  calc Real.sin (2 * x)
      = 2 * Real.sin x * Real.cos x := hsin2
    _ = 2 * Real.sin x * Real.cos x
        / (Real.sin x ^ 2 + Real.cos x ^ 2) := by
          rw [hsq]
          ring
    _ = 2 * (Real.sin x / Real.cos x)
        / (1 + (Real.sin x / Real.cos x) ^ 2) := by
          field_simp
          ring
    _ = s32_of_t (Real.sin x / Real.cos x) := by
          unfold s32_of_t
          ring
    _ = s32_of_t (Real.tan x) := by rw [← htan]

theorem eq_of_abs_lt {x : ℝ} (hx : |x| < Real.pi / 4) :
    (∑' k : ℕ, chapter9Entry32LeftTerm x k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  have hx_le : |x| ≤ Real.pi / 4 := le_of_lt hx
  have ht : ‖Real.tan x‖ < 1 := tan_abs_lt_one_of_abs_lt hx
  have hsin := sin_two_eq_s32_of_tan hx_le
  have hF := F32_s32_eq ht
  rw [tsum_left_eq_F32, tsum_tan_eq_G32, hsin]
  exact hF

theorem continuousOn_F32_Icc :
    ContinuousOn F32 (Set.Icc (-1 : ℝ) 1) := by
  have hu : Summable
      (fun k : ℕ => (2:ℝ) ^ ((1/4 : ℝ))
        * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) :=
    summable32_maj54.mul_left _
  apply continuousOn_tsum (fun k => ?_) hu (fun k s hs => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * k + 1)).continuousOn
  · have hs1 : |s| ≤ 1 := by
      have hmem := Set.mem_Icc.mp hs
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    have hpow : |s| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hs1
    have hCnn : (0:ℝ) ≤ (2:ℝ) ^ ((1/4 : ℝ)) := by positivity
    have hMnn : (0:ℝ) ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by positivity
    have hD2pos : (0:ℝ) < (((k : ℝ) + 1) ^ (2:ℕ)) := by positivity
    have hDle : (((k : ℝ) + 1) ^ (2:ℕ))
        ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ)) := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      push_cast at h ⊢
      linarith
    have hMdiv : (((k : ℝ) + 1) ^ ((3/4 : ℝ)))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ))
        ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ)) :=
      div_le_div_of_nonneg_left hMnn hD2pos hDle
    have hB : bCoeff32 k * |s| ^ (2 * k + 1) ≤ bCoeff32 k := by
      have hle : |s| ^ (2 * k + 1) ≤ 1 := hpow
      calc bCoeff32 k * |s| ^ (2 * k + 1)
          ≤ bCoeff32 k * 1 :=
            mul_le_mul_of_nonneg_left hle (le_of_lt (bCoeff32_pos k))
        _ = bCoeff32 k := mul_one _
    have hnorm : ‖bCoeff32 k * s ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖
        = bCoeff32 k * |s| ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_of_lt (bCoeff32_pos k)),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n := 2 * k + 1))]
    rw [hnorm]
    calc bCoeff32 k * |s| ^ (2 * k + 1) / ((((2*k+1:ℕ)):ℝ) ^ 2)
        ≤ bCoeff32 k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hB (by positivity)
      _ ≤ ((2:ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right (bCoeff32_le_rpow k) (by positivity)
      _ = (2:ℝ) ^ ((1/4 : ℝ))
          * ((((k : ℝ) + 1) ^ ((3/4 : ℝ)))
            / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
          rw [mul_div_assoc]
      _ ≤ (2:ℝ) ^ ((1/4 : ℝ))
          * ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left hMdiv hCnn
      _ = (2:ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
          rw [rpow32_div_eq]

theorem continuousOn_G32_Icc :
    ContinuousOn G32 (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun k => ?_) summable32_maj2
    (fun k t ht => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * k + 1)).continuousOn
  · have ht1 : |t| ≤ 1 := by
      have hmem := Set.mem_Icc.mp ht
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    have hpow : |(-1 : ℝ) ^ k * t ^ (2 * k + 1)| ≤ 1 := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact pow_le_one₀ (abs_nonneg _) ht1
    have hDle : (((k : ℝ) + 1) ^ 2)
        ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      have heq : ((((2 * k + 1 : ℕ)) : ℝ)) = 2 * (k : ℝ) + 1 := by
        push_cast
        ring
      rw [heq]
      have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith [hk]
    have hqpos : (0:ℝ) < (((k : ℝ) + 1) ^ 2) := by positivity
    have hnorm : ‖(-1 : ℝ) ^ k * t ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖
        = |(-1 : ℝ) ^ k * t ^ (2 * k + 1)|
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      simp only [norm_div, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((((2*k+1:ℕ)):ℝ)^2))]
    rw [hnorm]
    calc |(-1 : ℝ) ^ k * t ^ (2 * k + 1)|
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
        ≤ 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le hqpos hDle

theorem continuousOn_LHS32 :
    ContinuousOn (fun x : ℝ => F32 (Real.sin (2 * x)))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  have hsin : Continuous (fun x : ℝ => Real.sin (2 * x)) := by continuity
  have hmem : ∀ x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4),
      Real.sin (2 * x) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x _
    have h1 : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
    rw [abs_le] at h1
    rw [Set.mem_Icc]
    constructor <;> linarith [h1.1, h1.2]
  have hcomp := continuousOn_F32_Icc.comp hsin.continuousOn hmem
  have e : (F32 ∘ (fun x : ℝ => Real.sin (2 * x)))
      = fun x : ℝ => F32 (Real.sin (2 * x)) := by
    funext x
    rfl
  rw [e] at hcomp
  exact hcomp

theorem continuousOn_RHS32 :
    ContinuousOn (fun x : ℝ => G32 (Real.tan x))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  have htan : ContinuousOn Real.tan (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
    have hsub : Set.Icc (-Real.pi / 4) (Real.pi / 4)
        ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro x hx
      have hmem := Set.mem_Icc.mp hx
      rw [Set.mem_Ioo]
      constructor <;> (have := Real.pi_pos; linarith [hmem.1, hmem.2])
    exact Real.continuousOn_tan_Ioo.mono hsub
  have hmem : ∀ x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4),
      Real.tan x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hmemIcc := Set.mem_Icc.mp hx
    have habs : |x| ≤ Real.pi / 4 := by
      rw [abs_le]
      constructor <;> linarith [hmemIcc.1, hmemIcc.2]
    have htan := tan32_abs_le x habs
    rw [abs_le] at htan
    rw [Set.mem_Icc]
    constructor <;> linarith [htan.1, htan.2]
  have hcomp := continuousOn_G32_Icc.comp htan hmem
  have e : (G32 ∘ Real.tan) = fun x : ℝ => G32 (Real.tan x) := by
    funext x
    rfl
  rw [e] at hcomp
  exact hcomp

theorem continuousOn_RHS32mul :
    ContinuousOn (fun x : ℝ => 2 * G32 (Real.tan x))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) :=
  continuousOn_RHS32.const_mul 2

theorem tendsto_one_div_succ :
    Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hcomp := h1.comp hsucc
  have e : (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) ∘ (fun n : ℕ => n + 1)
      = fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2) := by
    funext n
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [e] at hcomp
  exact hcomp

theorem eq_at_pi_div_four :
    (∑' k : ℕ, chapter9Entry32LeftTerm (Real.pi / 4) k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm (Real.pi / 4) k := by
  have hIcc : (Real.pi / 4) ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    rw [Set.mem_Icc]
    constructor
    · have := Real.pi_pos
      linarith
    · linarith
  have useq : ∀ n : ℕ, Real.pi / 4 - 1 / ((n : ℝ) + 2)
      ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hle : (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) _
      linarith [hN]
    have hpi : (1:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    constructor
    · linarith [hpos, hle, hpi]
    · linarith [hpos]
  have useq_Icc : ∀ n : ℕ, Real.pi / 4 - 1 / ((n : ℝ) + 2)
      ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    exact Set.Ioo_subset_Icc_self (useq n)
  have hlim : Tendsto (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))
      atTop (𝓝 (Real.pi / 4)) := by
    have h1 : Tendsto (fun _ : ℕ => (Real.pi / 4 : ℝ)) atTop
        (𝓝 (Real.pi / 4)) :=
      tendsto_const_nhds
    have h := h1.sub tendsto_one_div_succ
    simpa [sub_zero] using h
  have hwithin : Tendsto (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))
      atTop (𝓝[Set.Icc (-Real.pi / 4) (Real.pi / 4)] (Real.pi / 4)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hlim (Filter.Eventually.of_forall useq_Icc)
  have hLHScont := continuousOn_LHS32.continuousWithinAt hIcc
  have hRHScont := continuousOn_RHS32mul.continuousWithinAt hIcc
  have hLHSlim : Tendsto
      ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (F32 (Real.sin (2 * (Real.pi / 4))))) :=
    hLHScont.tendsto.comp hwithin
  have hRHSlim : Tendsto
      ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (2 * G32 (Real.tan (Real.pi / 4)))) :=
    hRHScont.tendsto.comp hwithin
  have hEq : ∀ n : ℕ, F32 (Real.sin (2 * (Real.pi / 4 - 1 / ((n : ℝ) + 2))))
      = 2 * G32 (Real.tan (Real.pi / 4 - 1 / ((n : ℝ) + 2))) := by
    intro n
    have hmem := useq n
    have habs : |Real.pi / 4 - 1 / ((n : ℝ) + 2)| < Real.pi / 4 := by
      have hmemIoo := Set.mem_Ioo.mp hmem
      rw [abs_lt]
      constructor <;> linarith [hmemIoo.1, hmemIoo.2]
    have heq := eq_of_abs_lt habs
    rw [tsum_left_eq_F32, tsum_tan_eq_G32] at heq
    exact heq
  have hEqFun : ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      = ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))) := by
    funext n
    simp only [Function.comp_apply]
    exact hEq n
  rw [hEqFun] at hLHSlim
  have hUnique : F32 (Real.sin (2 * (Real.pi / 4)))
      = 2 * G32 (Real.tan (Real.pi / 4)) :=
    tendsto_nhds_unique hLHSlim hRHSlim
  rw [tsum_left_eq_F32, tsum_tan_eq_G32]
  exact hUnique

theorem eq_at_neg_pi_div_four :
    (∑' k : ℕ, chapter9Entry32LeftTerm (-Real.pi / 4) k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm (-Real.pi / 4) k := by
  have hIcc : (-Real.pi / 4) ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    rw [Set.mem_Icc]
    constructor
    · linarith
    · have := Real.pi_pos
      linarith
  have vseq : ∀ n : ℕ, -Real.pi / 4 + 1 / ((n : ℝ) + 2)
      ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hle : (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) _
      linarith [hN]
    have hpi : (1:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    constructor
    · linarith [hpos]
    · linarith [hpos, hle, hpi]
  have vseq_Icc : ∀ n : ℕ, -Real.pi / 4 + 1 / ((n : ℝ) + 2)
      ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    exact Set.Ioo_subset_Icc_self (vseq n)
  have hlim : Tendsto (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))
      atTop (𝓝 (-Real.pi / 4)) := by
    have h1 : Tendsto (fun _ : ℕ => (-Real.pi / 4 : ℝ)) atTop
        (𝓝 (-Real.pi / 4)) :=
      tendsto_const_nhds
    have h := h1.add tendsto_one_div_succ
    simpa [add_zero] using h
  have hwithin : Tendsto (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))
      atTop (𝓝[Set.Icc (-Real.pi / 4) (Real.pi / 4)] (-Real.pi / 4)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hlim (Filter.Eventually.of_forall vseq_Icc)
  have hLHScont := continuousOn_LHS32.continuousWithinAt hIcc
  have hRHScont := continuousOn_RHS32mul.continuousWithinAt hIcc
  have hLHSlim : Tendsto
      ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (F32 (Real.sin (2 * (-Real.pi / 4))))) :=
    hLHScont.tendsto.comp hwithin
  have hRHSlim : Tendsto
      ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (2 * G32 (Real.tan (-Real.pi / 4)))) :=
    hRHScont.tendsto.comp hwithin
  have hEq : ∀ n : ℕ, F32 (Real.sin (2 * (-Real.pi / 4 + 1 / ((n : ℝ) + 2))))
      = 2 * G32 (Real.tan (-Real.pi / 4 + 1 / ((n : ℝ) + 2))) := by
    intro n
    have hmem := vseq n
    have habs : |-Real.pi / 4 + 1 / ((n : ℝ) + 2)| < Real.pi / 4 := by
      have hmemIoo := Set.mem_Ioo.mp hmem
      rw [abs_lt]
      constructor <;> linarith [hmemIoo.1, hmemIoo.2]
    have heq := eq_of_abs_lt habs
    rw [tsum_left_eq_F32, tsum_tan_eq_G32] at heq
    exact heq
  have hEqFun : ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      = ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))) := by
    funext n
    simp only [Function.comp_apply]
    exact hEq n
  rw [hEqFun] at hLHSlim
  have hUnique : F32 (Real.sin (2 * (-Real.pi / 4)))
      = 2 * G32 (Real.tan (-Real.pi / 4)) :=
    tendsto_nhds_unique hLHSlim hRHSlim
  rw [tsum_left_eq_F32, tsum_tan_eq_G32]
  exact hUnique

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry32_lambertdivisor`.
-/
theorem ramanujan_part1_ch9_entry32_lambertdivisor (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    0 < Real.cos x ∧
      Summable (chapter9Entry32LeftTerm x) ∧
      Summable (chapter9Entry19TanTerm x) ∧
      (∑' k : ℕ, chapter9Entry32LeftTerm x k) =
        2 * ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  refine ⟨cos32_pos x hx, summable32_left x, summable32_tan x hx, ?_⟩
  by_cases hlt : |x| < Real.pi / 4
  · exact eq_of_abs_lt hlt
  · have hEq : |x| = Real.pi / 4 := le_antisymm hx (le_of_not_gt hlt)
    by_cases hx0 : 0 ≤ x
    · have hxAbs : |x| = x := abs_of_nonneg hx0
      have hxPi : x = Real.pi / 4 := by linarith [hEq, hxAbs]
      rw [hxPi]
      exact eq_at_pi_div_four
    · have hxNeg : x < 0 := lt_of_not_ge hx0
      have hxAbs : |x| = -x := abs_of_neg hxNeg
      have hxPi : x = -Real.pi / 4 := by linarith [hEq, hxAbs]
      rw [hxPi]
      exact eq_at_neg_pi_div_four

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
