/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.BigOperators.Fin
import Def.Analysis.Calculus.ArcsinDivSinIntegral
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

lemma ads_halfArcsinSinSq_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsHalfArcsinSinSq (adsHalfArcsinSinSqDeriv x) x := by
  rw [Set.mem_Ioo] at hx
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx.2⟩
  have hsin_sq_lt : Real.sin x ^ 2 < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_pos hcos]
  have hne_neg : Real.sin x ^ 2 ≠ -1 := by
    nlinarith [sq_nonneg (Real.sin x)]
  have hne_one : Real.sin x ^ 2 ≠ 1 := ne_of_lt hsin_sq_lt
  have hinner := (Real.hasDerivAt_sin x).pow 2
  have hcomp := (Real.hasDerivAt_arcsin hne_neg hne_one).comp x hinner
  have hfactor : 1 - (Real.sin x ^ 2) ^ 2 =
      Real.cos x ^ 2 * (1 + Real.sin x ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hsqrt : Real.sqrt (1 - (Real.sin x ^ 2) ^ 2) =
      Real.cos x * Real.sqrt (1 + Real.sin x ^ 2) := by
    rw [hfactor, Real.sqrt_mul (sq_nonneg (Real.cos x)), Real.sqrt_sq hcos.le]
  rw [hsqrt] at hcomp
  have hsqrt_pos : 0 < Real.sqrt (1 + Real.sin x ^ 2) := by positivity
  have hfun : adsHalfArcsinSinSq =
      fun y => (Real.arcsin ∘ (Real.sin ^ 2)) y / 2 := by
    funext y
    simp [adsHalfArcsinSinSq, Function.comp_apply]
  rw [hfun]
  change HasDerivAt _ (Real.sin x / Real.sqrt (1 + Real.sin x ^ 2)) x
  convert hcomp.div_const 2 using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [ne_of_gt hcos, ne_of_gt hsqrt_pos]

lemma ads_halfArcsinSinSq_continuous : Continuous adsHalfArcsinSinSq := by
  exact (Real.continuous_arcsin.comp (Real.continuous_sin.pow 2)).div_const 2

lemma ads_halfArcsinSinSq_endpoints :
    adsHalfArcsinSinSq 0 = 0 ∧
      adsHalfArcsinSinSq (Real.pi / 2) = Real.pi / 4 := by
  constructor
  · simp [adsHalfArcsinSinSq]
  · rw [adsHalfArcsinSinSq, Real.sin_pi_div_two, one_pow, Real.arcsin_one]
    ring

lemma ads_halfArcsinSinSqDeriv_nonneg {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ adsHalfArcsinSinSqDeriv x := by
  rw [Set.mem_Ioo] at hx
  unfold adsHalfArcsinSinSqDeriv
  exact div_nonneg
    (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])))
    (Real.sqrt_nonneg _)

lemma ads_substitution_integrand_eq {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    (adsRawIntegrand ∘ adsHalfArcsinSinSq) x * adsHalfArcsinSinSqDeriv x =
      Real.arcsin (Real.sin x ^ 2) / Real.sin x := by
  rw [Set.mem_Ioo] at hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  have hsin_sq_le : Real.sin x ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
  have hsin_arcsin : Real.sin (Real.arcsin (Real.sin x ^ 2)) = Real.sin x ^ 2 :=
    Real.sin_arcsin (by nlinarith [sq_nonneg (Real.sin x)]) hsin_sq_le
  have hsqrt : 0 < Real.sqrt (1 + Real.sin x ^ 2) := by positivity
  simp only [Function.comp_apply, adsRawIntegrand, adsHalfArcsinSinSqDeriv,
    adsHalfArcsinSinSq]
  rw [show 2 * (Real.arcsin (Real.sin x ^ 2) / 2) =
    Real.arcsin (Real.sin x ^ 2) by ring, hsin_arcsin]
  field_simp [ne_of_gt hsin, ne_of_gt hsqrt]

lemma ads_integral_eq_raw :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      ∫ x in (0 : ℝ)..(Real.pi / 4), adsRawIntegrand x := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := adsHalfArcsinSinSq)
    (f' := adsHalfArcsinSinSqDeriv) (g := adsRawIntegrand)
    ads_halfArcsinSinSq_continuous.continuousOn
    (fun x hx => ads_halfArcsinSinSq_hasDerivAt (by
      simpa [min_eq_left hpi, max_eq_right hpi] using hx))
    (fun x hx => ads_halfArcsinSinSqDeriv_nonneg (by
      simpa [min_eq_left hpi, max_eq_right hpi] using hx))
  rw [ads_halfArcsinSinSq_endpoints.1, ads_halfArcsinSinSq_endpoints.2] at hchange
  calc
    (∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
        ∫ x in (0 : ℝ)..(Real.pi / 2),
          (adsRawIntegrand ∘ adsHalfArcsinSinSq) x *
            adsHalfArcsinSinSqDeriv x := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [Filter.self_mem_codiscreteWithin
        (Set.uIoc (0 : ℝ) (Real.pi / 2)),
        compl_singleton_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) (Real.pi / 2))
          (Real.pi / 2)] with x hx hne
      rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact (ads_substitution_integrand_eq
        ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩).symm
    _ = ∫ x in (0 : ℝ)..(Real.pi / 4), adsRawIntegrand x := hchange

lemma ads_sqrt_one_add_sin_two_mul {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    Real.sqrt (1 + Real.sin (2 * x)) = Real.sin x + Real.cos x := by
  rw [Set.mem_Icc] at hx
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos x := le_of_lt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  have hsq : 1 + Real.sin (2 * x) = (Real.sin x + Real.cos x) ^ 2 := by
    rw [Real.sin_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg hsin hcos)]

lemma ads_rawIntegrand_eq_j {x : ℝ}
    (hx : x ∈ Set.Ioc 0 (Real.pi / 4)) :
    adsRawIntegrand x = adsJIntegrand x := by
  rw [Set.mem_Ioc] at hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rw [adsRawIntegrand, adsJIntegrand,
    ads_sqrt_one_add_sin_two_mul ⟨le_of_lt hx.1, hx.2⟩, Real.sin_two_mul]
  field_simp [ne_of_gt hsin, ne_of_gt hcos]

lemma ads_integral_eq_j :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      ∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x := by
  rw [ads_integral_eq_raw]
  apply intervalIntegral.integral_congr_codiscreteWithin
  filter_upwards [Filter.self_mem_codiscreteWithin
    (Set.uIoc (0 : ℝ) (Real.pi / 4))] with x hx
  rw [Set.uIoc_of_le (by positivity)] at hx
  exact ads_rawIntegrand_eq_j hx

lemma ads_logTanHalf_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsLogTanHalf (1 / Real.sin x) x := by
  rw [Set.mem_Ioo] at hx
  have hu : x / 2 ∈ Set.Ioo 0 (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hsin : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos])
  have hcos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩
  have htan : 0 < Real.tan (x / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hinner : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  have htan_deriv := (Real.hasDerivAt_tan (ne_of_gt hcos)).comp x hinner
  have hlog := (Real.hasDerivAt_log (ne_of_gt htan)).comp x htan_deriv
  have hsin_two : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    nth_rewrite 1 [show x = 2 * (x / 2) by ring]
    rw [Real.sin_two_mul]
  have hval : (Real.tan (x / 2))⁻¹ *
      (1 / Real.cos (x / 2) ^ 2 * (1 / 2)) = 1 / Real.sin x := by
    rw [Real.tan_eq_sin_div_cos, hsin_two]
    field_simp [ne_of_gt hsin, ne_of_gt hcos]
  rw [hval] at hlog
  have hfun : adsLogTanHalf = Real.log ∘ Real.tan ∘ fun y : ℝ => y / 2 := by
    funext y
    rfl
  rw [hfun]
  exact hlog

lemma ads_logTanShift_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsLogTanShift (1 / Real.cos x) x := by
  rw [Set.mem_Ioo] at hx
  let u := x / 2 + Real.pi / 4
  have hu : u ∈ Set.Ioo 0 (Real.pi / 2) := by
    dsimp [u]
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  have hsin : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos])
  have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩
  have htan : 0 < Real.tan u := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hinner : HasDerivAt (fun y : ℝ => y / 2 + Real.pi / 4) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2 |>.add_const (Real.pi / 4)
  have htan_deriv := (Real.hasDerivAt_tan (ne_of_gt hcos)).comp x hinner
  have hlog := (Real.hasDerivAt_log (ne_of_gt htan)).comp x htan_deriv
  have hsin_two : Real.sin (2 * u) = Real.cos x := by
    rw [show 2 * u = x + Real.pi / 2 by dsimp [u]; ring, Real.sin_add_pi_div_two]
  have hval : (Real.tan u)⁻¹ * (1 / Real.cos u ^ 2 * (1 / 2)) =
      1 / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos, ← hsin_two, Real.sin_two_mul]
    field_simp [ne_of_gt hsin, ne_of_gt hcos]
  rw [hval] at hlog
  have hfun : adsLogTanShift = Real.log ∘ Real.tan ∘
      fun y : ℝ => y / 2 + Real.pi / 4 := by
    funext y
    rfl
  rw [hfun]
  exact hlog

lemma ads_sinc_pos_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) : 0 < Real.sinc x := by
  by_cases hzero : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hzero]
    rw [Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    exact div_pos
      (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, Real.pi_pos])) hxpos

lemma ads_sin_eq_mul_sinc (x : ℝ) :
    Real.sin x = x * Real.sinc x := by
  by_cases hzero : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hzero]
    field_simp

lemma ads_intervalIntegrable_x_div_sin :
    IntervalIntegrable (fun x : ℝ => x / Real.sin x) volume 0 (Real.pi / 4) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hcont : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      (Set.uIcc 0 (Real.pi / 4)) := by
    apply Real.continuous_sinc.continuousOn.inv₀
    intro x hx
    apply ne_of_gt
    apply ads_sinc_pos_of_mem_Icc
    simpa [Set.uIcc_of_le hpi] using hx
  have hint : IntervalIntegrable (fun x : ℝ => (Real.sinc x)⁻¹)
      volume 0 (Real.pi / 4) := hcont.intervalIntegrable
  have heq : Set.EqOn (fun x : ℝ => x / Real.sin x)
      (fun x : ℝ => (Real.sinc x)⁻¹) (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le hpi, Set.mem_Ioc] at hx
    change x / Real.sin x = (Real.sinc x)⁻¹
    rw [ads_sin_eq_mul_sinc]
    field_simp [ne_of_gt hx.1]
  exact (intervalIntegrable_congr heq).mpr hint

lemma ads_intervalIntegrable_x_div_cos :
    IntervalIntegrable (fun x : ℝ => x / Real.cos x) volume 0 (Real.pi / 4) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_id.div Real.continuous_cos.continuousOn
  intro x hx
  rw [Set.uIcc_of_le hpi, Set.mem_Icc] at hx
  apply ne_of_gt
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩

lemma ads_logTanHalf_intervalIntegrable :
    IntervalIntegrable adsLogTanHalf volume 0 (Real.pi / 4) := by
  have hsin : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (x / 2)))
      volume 0 (Real.pi / 4) := by
    convert
      (intervalIntegrable_log_sin (a := (0 : ℝ)) (b := Real.pi / 8)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> ring_nf
  have hcos : IntervalIntegrable (fun x : ℝ => Real.log (Real.cos (x / 2)))
      volume 0 (Real.pi / 4) := by
    convert
      (intervalIntegrable_log_cos (a := (0 : ℝ)) (b := Real.pi / 8)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> ring_nf
  have hsub := hsin.sub hcos
  have heq : Set.EqOn
      (fun x : ℝ => Real.log (Real.sin (x / 2)) - Real.log (Real.cos (x / 2)))
      adsLogTanHalf (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
    have hs : Real.sin (x / 2) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos]))
    have hc : Real.cos (x / 2) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    unfold adsLogTanHalf
    rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]
  exact (intervalIntegrable_congr heq).mp hsub

lemma ads_logTanShift_intervalIntegrable :
    IntervalIntegrable adsLogTanShift volume 0 (Real.pi / 4) := by
  have hsin : IntervalIntegrable
      (fun x : ℝ => Real.log (Real.sin (x / 2 + Real.pi / 4)))
      volume 0 (Real.pi / 4) := by
    convert ((intervalIntegrable_log_sin (a := Real.pi / 4)
      (b := 3 * Real.pi / 8)).comp_add_right (Real.pi / 4)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> try ring_nf
    funext x
    rw [add_comm]
  have hcos : IntervalIntegrable
      (fun x : ℝ => Real.log (Real.cos (x / 2 + Real.pi / 4)))
      volume 0 (Real.pi / 4) := by
    convert ((intervalIntegrable_log_cos (a := Real.pi / 4)
      (b := 3 * Real.pi / 8)).comp_add_right (Real.pi / 4)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> try ring_nf
    funext x
    rw [add_comm]
  have hsub := hsin.sub hcos
  have heq : Set.EqOn
      (fun x : ℝ => Real.log (Real.sin (x / 2 + Real.pi / 4)) -
        Real.log (Real.cos (x / 2 + Real.pi / 4)))
      adsLogTanShift (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
    have hu : x / 2 + Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := by
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    have hs : Real.sin (x / 2 + Real.pi / 4) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos]))
    have hc : Real.cos (x / 2 + Real.pi / 4) ≠ 0 := ne_of_gt
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩)
    unfold adsLogTanShift
    rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]
  exact (intervalIntegrable_congr heq).mp hsub

lemma ads_halfProduct_continuousOn :
    ContinuousOn (fun x : ℝ => x * adsLogTanHalf x) (Set.Icc 0 (Real.pi / 4)) := by
  have harg : Continuous fun x : ℝ => x / 2 := continuous_id.div_const 2
  have hmulLog : Continuous fun x : ℝ =>
      2 * ((x / 2) * Real.log (x / 2)) := by
    exact continuous_const.mul (Real.continuous_mul_log.comp harg)
  have hlogSinc : ContinuousOn (fun x : ℝ => Real.log (Real.sinc (x / 2)))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_log.comp (Real.continuous_sinc.comp harg).continuousOn
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    apply ne_of_gt
    apply ads_sinc_pos_of_mem_Icc
    rw [Set.mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hlogCos : ContinuousOn (fun x : ℝ => Real.log (Real.cos (x / 2)))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_log.comp (Real.continuous_cos.comp harg).continuousOn
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Set.mem_Icc] at hx
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  have hrhs : ContinuousOn (fun x : ℝ =>
      2 * ((x / 2) * Real.log (x / 2)) + x * Real.log (Real.sinc (x / 2)) -
        x * Real.log (Real.cos (x / 2))) (Set.Icc 0 (Real.pi / 4)) :=
    hmulLog.continuousOn.add (continuousOn_id.mul hlogSinc) |>.sub
      (continuousOn_id.mul hlogCos)
  apply hrhs.congr
  intro x hx
  by_cases hzero : x = 0
  · subst x
    simp [adsLogTanHalf]
  · rw [Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    have hhalf : x / 2 ≠ 0 := by positivity
    have hsinc : Real.sinc (x / 2) ≠ 0 := ne_of_gt (ads_sinc_pos_of_mem_Icc <| by
      rw [Set.mem_Icc]
      constructor <;> linarith [hx.1, hx.2])
    have hsin : Real.sin (x / 2) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by linarith [hx.2, Real.pi_pos]))
    have hcos : Real.cos (x / 2) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hxpos, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    change x * Real.log (Real.tan (x / 2)) =
      2 * ((x / 2) * Real.log (x / 2)) + x * Real.log (Real.sinc (x / 2)) -
        x * Real.log (Real.cos (x / 2))
    rw [Real.tan_eq_sin_div_cos, Real.log_div hsin hcos,
      ads_sin_eq_mul_sinc, Real.log_mul hhalf hsinc]
    ring

lemma ads_logTanShift_continuousOn :
    ContinuousOn adsLogTanShift (Set.Icc 0 (Real.pi / 4)) := by
  have harg : Continuous fun x : ℝ => x / 2 + Real.pi / 4 :=
    (continuous_id.div_const 2).add continuous_const
  have htan : ContinuousOn (fun x : ℝ => Real.tan (x / 2 + Real.pi / 4))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_tan_Ioo.comp harg.continuousOn
    intro x hx
    rw [Set.mem_Icc] at hx
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  unfold adsLogTanShift
  apply Real.continuousOn_log.comp htan
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [Set.mem_Icc] at hx
  have hs : 0 < Real.sin (x / 2 + Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, Real.pi_pos])
      (by linarith [hx.2, Real.pi_pos])
  have hc : 0 < Real.cos (x / 2 + Real.pi / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos]
  exact ne_of_gt (div_pos hs hc)

lemma ads_logTanProducts_continuousOn :
    ContinuousOn adsLogTanProducts (Set.Icc 0 (Real.pi / 4)) := by
  unfold adsLogTanProducts
  exact ads_halfProduct_continuousOn.add
    (continuousOn_id.mul ads_logTanShift_continuousOn)

lemma ads_logTanProducts_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt adsLogTanProducts
      (adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x) x := by
  have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hhalf := (hasDerivAt_id x).mul (ads_logTanHalf_hasDerivAt hx')
  have hshift := (hasDerivAt_id x).mul (ads_logTanShift_hasDerivAt hx')
  change HasDerivAt (fun y : ℝ =>
    y * adsLogTanHalf y + y * adsLogTanShift y) _ x
  have hfun : (id * adsLogTanHalf + id * adsLogTanShift : ℝ → ℝ) =
      fun y : ℝ => y * adsLogTanHalf y + y * adsLogTanShift y := by
    funext y
    rfl
  rw [← hfun]
  simpa only [Pi.add_apply, Pi.mul_apply, id_eq, one_mul, div_eq_mul_inv,
    add_assoc] using hhalf.add hshift

lemma ads_logTanProducts_deriv_intervalIntegrable :
    IntervalIntegrable (fun x : ℝ =>
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x)
      volume 0 (Real.pi / 4) :=
  ((ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin).add
    ads_logTanShift_intervalIntegrable).add ads_intervalIntegrable_x_div_cos

lemma ads_logTanProducts_endpoints :
    adsLogTanProducts 0 = 0 ∧ adsLogTanProducts (Real.pi / 4) = 0 := by
  constructor
  · simp [adsLogTanProducts]
  · have ht : Real.tan (3 * Real.pi / 8) = (Real.tan (Real.pi / 8))⁻¹ := by
      rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
        Real.tan_pi_div_two_sub]
    have hlogs : Real.log (Real.tan (Real.pi / 8)) +
        Real.log (Real.tan (3 * Real.pi / 8)) = 0 := by
      rw [ht, Real.log_inv, add_neg_cancel]
    rw [adsLogTanProducts, adsLogTanHalf, adsLogTanShift,
      show (Real.pi / 4) / 2 = Real.pi / 8 by ring,
      show Real.pi / 8 + Real.pi / 4 = 3 * Real.pi / 8 by ring]
    calc
      Real.pi / 4 * Real.log (Real.tan (Real.pi / 8)) +
          Real.pi / 4 * Real.log (Real.tan (3 * Real.pi / 8)) =
          Real.pi / 4 * (Real.log (Real.tan (Real.pi / 8)) +
            Real.log (Real.tan (3 * Real.pi / 8))) := by ring
      _ = 0 := by rw [hlogs, mul_zero]

lemma ads_logTan_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (Real.tan x)) volume a b := by
  have hsub := (intervalIntegrable_log_sin (a := a) (b := b)).sub
    (intervalIntegrable_log_cos (a := a) (b := b))
  have hsin : Real.sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := Real.pi / 2) (by simp)
  have hcos : Real.cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0) (by simp)
  apply hsub.congr_codiscreteWithin
  filter_upwards [Filter.codiscreteWithin_mono (Set.subset_univ _) hsin,
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcos] with x hs hc
  simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
    Set.mem_singleton_iff] at hs hc
  simp only [Function.comp_apply]
  rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]

lemma ads_integral_log_terms_and_j_eq_zero :
    (∫ x in (0 : ℝ)..(Real.pi / 4),
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x) = 0 := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := Real.pi / 4) (f := adsLogTanProducts)
    (f' := fun x : ℝ =>
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x)
    (by positivity) ads_logTanProducts_continuousOn
    (fun x hx => ads_logTanProducts_hasDerivAt hx)
    ads_logTanProducts_deriv_intervalIntegrable
  rw [ads_logTanProducts_endpoints.1, ads_logTanProducts_endpoints.2, sub_zero] at hftc
  exact hftc

lemma ads_j_eq_log_integrals :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x) =
      -(∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanHalf x) -
        ∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x := by
  have hzero := ads_integral_log_terms_and_j_eq_zero
  rw [intervalIntegral.integral_add
      ((ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin).add
        ads_logTanShift_intervalIntegrable)
      ads_intervalIntegrable_x_div_cos,
    intervalIntegral.integral_add
      (ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin)
      ads_logTanShift_intervalIntegrable,
    intervalIntegral.integral_add ads_logTanHalf_intervalIntegrable
      ads_intervalIntegrable_x_div_sin] at hzero
  have hj : (∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x) =
      (∫ x in (0 : ℝ)..(Real.pi / 4), x / Real.cos x) +
        ∫ x in (0 : ℝ)..(Real.pi / 4), x / Real.sin x := by
    rw [← intervalIntegral.integral_add ads_intervalIntegrable_x_div_cos
      ads_intervalIntegrable_x_div_sin]
    apply intervalIntegral.integral_congr
    intro x _
    unfold adsJIntegrand
    ring
  rw [hj]
  linarith

lemma ads_integral_logTanHalf :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanHalf x) =
      2 * adsLogTanIntegral (Real.pi / 8) := by
  unfold adsLogTanHalf adsLogTanIntegral
  convert intervalIntegral.integral_comp_div
    (a := (0 : ℝ)) (b := Real.pi / 4) (c := (2 : ℝ))
    (fun x : ℝ => Real.log (Real.tan x)) (by norm_num) using 1
  all_goals norm_num
  all_goals ring_nf

lemma ads_integral_logTanShift :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x) =
      2 * (adsLogTanIntegral (3 * Real.pi / 8) -
        adsLogTanIntegral (Real.pi / 4)) := by
  have hcomp : (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x) =
      2 * ∫ x in (Real.pi / 4)..(3 * Real.pi / 8),
        Real.log (Real.tan x) := by
    unfold adsLogTanShift
    convert intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := Real.pi / 4) (c := (1 / 2 : ℝ))
      (fun x : ℝ => Real.log (Real.tan x)) (by norm_num) (Real.pi / 4) using 1
    all_goals norm_num
    all_goals ring_nf
    apply intervalIntegral.integral_congr
    intro x _
    change Real.log (Real.tan (x * (1 / 2) + Real.pi * (1 / 4))) =
      Real.log (Real.tan (Real.pi * (1 / 4) + x * (1 / 2)))
    rw [add_comm]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (ads_logTan_intervalIntegrable 0 (Real.pi / 4))
    (ads_logTan_intervalIntegrable (Real.pi / 4) (3 * Real.pi / 8))
  unfold adsLogTanIntegral
  rw [hcomp]
  linarith

lemma ads_logTan_reflection (a : ℝ) :
    (∫ x in (Real.pi / 2 - a)..(Real.pi / 2), Real.log (Real.tan x)) =
      -adsLogTanIntegral a := by
  have hfun : (fun x : ℝ => Real.log (Real.tan (Real.pi / 2 - x))) =
      fun x : ℝ => -Real.log (Real.tan x) := by
    funext x
    rw [Real.tan_pi_div_two_sub, Real.log_inv]
  have hsubst := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := a) (fun x : ℝ => Real.log (Real.tan x)) (Real.pi / 2)
  rw [hfun, intervalIntegral.integral_neg] at hsubst
  simpa [adsLogTanIntegral] using hsubst.symm

lemma ads_logTanIntegral_pi_div_two :
    adsLogTanIntegral (Real.pi / 2) = 0 := by
  have h : adsLogTanIntegral (Real.pi / 2) =
      -adsLogTanIntegral (Real.pi / 2) := by
    simpa [adsLogTanIntegral] using ads_logTan_reflection (Real.pi / 2)
  linarith

lemma ads_logTanIntegral_three_pi_div_eight :
    adsLogTanIntegral (3 * Real.pi / 8) = adsLogTanIntegral (Real.pi / 8) := by
  have href := ads_logTan_reflection (Real.pi / 8)
  rw [show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring] at href
  have hadd : adsLogTanIntegral (3 * Real.pi / 8) +
      (∫ x in (3 * Real.pi / 8)..(Real.pi / 2), Real.log (Real.tan x)) =
      adsLogTanIntegral (Real.pi / 2) := by
    simpa [adsLogTanIntegral] using intervalIntegral.integral_add_adjacent_intervals
      (ads_logTan_intervalIntegrable 0 (3 * Real.pi / 8))
      (ads_logTan_intervalIntegrable (3 * Real.pi / 8) (Real.pi / 2))
  rw [href, ads_logTanIntegral_pi_div_two] at hadd
  linarith

lemma ads_integral_eq_logTan_values :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      -4 * adsLogTanIntegral (Real.pi / 8) +
        2 * adsLogTanIntegral (Real.pi / 4) := by
  rw [ads_integral_eq_j, ads_j_eq_log_integrals, ads_integral_logTanHalf,
    ads_integral_logTanShift, ads_logTanIntegral_three_pi_div_eight]
  ring

lemma ads_base_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  exact h.comp_injective (by
    intro a b hab
    dsimp only at hab
    omega)

end
end Real.Calculus.ArcsinDivSinIntegral
