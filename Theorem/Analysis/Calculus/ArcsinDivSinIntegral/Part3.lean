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
import Def.Analysis.Calculus.ArcsinDivSinIntegral.Part3
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

lemma ads_SineSeries_eq_Sr_one (x : ℝ) :
    adsSineSeries x = adsSr 1 x := by
  unfold adsSineSeries adsSineTerm adsSr
  apply tsum_congr
  intro k
  simp

lemma ads_Rho_nonneg (n : ℕ) : 0 ≤ adsRho n := by
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one hden
  unfold adsRho
  linarith

lemma ads_Rho_lt_one (n : ℕ) : adsRho n < 1 := by
  unfold adsRho
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma ads_Rho_tendsto : Tendsto adsRho atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto adsRho atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h0
  simpa using h1

lemma ads_Rho_eventually_ge :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ adsRho n := by
  have h := ads_Rho_tendsto.eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h] with n hn
  exact le_of_lt hn

lemma ads_Sr_continuous_r (x : ℝ) :
    ContinuousOn (fun r : ℝ => adsSr r x) (Set.Icc 0 1) := by
  apply continuousOn_tsum (fun n => ?_) ads_base_summable
    (fun n r hr => ?_)
  · apply ContinuousOn.div_const
    exact (continuous_pow (2 * n + 1)).continuousOn.mul continuousOn_const
  · rw [Set.mem_Icc] at hr
    exact ads_Sr_norm_le r x hr.1 hr.2 n

lemma ads_Sr_tendsto_SineSeries (x : ℝ) :
    Tendsto (fun n : ℕ => adsSr (adsRho n) x) atTop (𝓝 (adsSineSeries x)) := by
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hev : ∀ᶠ n : ℕ in atTop, adsRho n ∈ Set.Icc 0 1 := by
    filter_upwards with n
    exact ⟨ads_Rho_nonneg n, le_of_lt (ads_Rho_lt_one n)⟩
  have hrho : Tendsto adsRho atTop (𝓝[Set.Icc 0 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ads_Rho_tendsto, hev⟩
  have hlim : Tendsto (fun n : ℕ => adsSr (adsRho n) x) atTop
      (𝓝 (adsSr 1 x)) :=
    Tendsto.comp (ads_Sr_continuous_r x 1 hmem) hrho
  rwa [← ads_SineSeries_eq_Sr_one x] at hlim

lemma ads_DrClosed_tendsto (t : ℝ)
    (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    Tendsto (fun n : ℕ => adsDrClosed (adsRho n) t) atTop
      (𝓝 (-Real.log (Real.tan t))) := by
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hnum : (1 : ℝ) + 2 * 1 * Real.cos (2 * t) + 1 ^ 2 =
      4 * Real.cos t ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  have hden : (1 : ℝ) - 2 * 1 * Real.cos (2 * t) + 1 ^ 2 =
      4 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul_eq_one_sub]
    ring
  have hval : adsDrClosed 1 t = -Real.log (Real.tan t) := by
    unfold adsDrClosed
    rw [hnum, hden]
    have hc0 : (0 : ℝ) < Real.cos t ^ 2 := pow_pos hcos 2
    have hs0 : (0 : ℝ) < Real.sin t ^ 2 := pow_pos hsin 2
    rw [Real.log_div (ne_of_gt (mul_pos (by norm_num) hc0))
        (ne_of_gt (mul_pos (by norm_num) hs0)),
      Real.log_mul (by norm_num) (ne_of_gt hc0),
      Real.log_mul (by norm_num) (ne_of_gt hs0),
      Real.log_pow, Real.log_pow]
    have htan_log : Real.log (Real.tan t) =
        Real.log (Real.sin t) - Real.log (Real.cos t) := by
      rw [Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hsin) (ne_of_gt hcos)]
    rw [htan_log]
    ring
  have hcont : ContinuousAt (fun r : ℝ => adsDrClosed r t) 1 := by
    unfold adsDrClosed
    have hN : ContinuousAt
        (fun r : ℝ => 1 + 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hM : ContinuousAt
        (fun r : ℝ => 1 - 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hMpos : (0 : ℝ) < 1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hden]
      positivity
    have hdiv : ContinuousAt
        (fun r : ℝ => (1 + 2 * r * Real.cos (2 * t) + r ^ 2) /
          (1 - 2 * r * Real.cos (2 * t) + r ^ 2)) 1 :=
      hN.div hM (ne_of_gt hMpos)
    have hNpos : (0 : ℝ) < 1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hnum]
      positivity
    have hratio : (1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2) /
        (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2) ≠ 0 :=
      div_ne_zero (ne_of_gt hNpos) (ne_of_gt hMpos)
    have hlog : Tendsto
        (fun r : ℝ => Real.log ((1 + 2 * r * Real.cos (2 * t) + r ^ 2) /
          (1 - 2 * r * Real.cos (2 * t) + r ^ 2)))
        (𝓝 1)
        (𝓝 (Real.log ((1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2) /
          (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2)))) :=
      (Real.continuousAt_log hratio).tendsto.comp hdiv.tendsto
    exact hlog.div_const 2
  have hcomp := hcont.tendsto.comp ads_Rho_tendsto
  rwa [hval] at hcomp

lemma ads_DrClosed_bound (r t : ℝ) (hr0 : (1 / 2 : ℝ) ≤ r)
    (hr1 : r ≤ 1) (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    ‖adsDrClosed r t‖ ≤ Real.log 2 - Real.log (Real.sin t) := by
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
  have hcos2 : Real.cos (2 * t) ≤ 1 := Real.cos_le_one _
  have hcos2nn : 0 ≤ Real.cos (2 * t) := by
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  unfold adsDrClosed
  set C : ℝ := Real.cos (2 * t) with hCdef
  set N : ℝ := 1 + 2 * r * C + r ^ 2 with hNdef
  set M : ℝ := 1 - 2 * r * C + r ^ 2 with hMdef
  have hr0' : (0 : ℝ) ≤ r := by linarith
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0' hr1
  have h2rC : (0 : ℝ) ≤ 2 * r * C := by positivity
  have hNlo : (1 : ℝ) ≤ N := by
    rw [hNdef]
    nlinarith [sq_nonneg r, h2rC]
  have hNhi : N ≤ 4 := by
    rw [hNdef]
    have h1 : 2 * r * C ≤ 2 := by
      have e1 : 2 * r ≤ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (by norm_num)
      have e2 : (2 * r) * C ≤ (2 * 1) * C :=
        mul_le_mul_of_nonneg_right e1 hcos2nn
      have e3 : (2 * 1) * C ≤ (2 * 1) * 1 :=
        mul_le_mul_of_nonneg_left hcos2 (by norm_num)
      calc
        (2 * r) * C ≤ (2 * 1) * C := e2
        _ ≤ (2 * 1) * 1 := e3
        _ = 2 := by norm_num
    linarith
  have hC2 : C = 1 - 2 * Real.sin t ^ 2 := by
    rw [hCdef, Real.cos_two_mul_eq_one_sub]
  have hMlo : 2 * Real.sin t ^ 2 ≤ M := by
    have hsq : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
    have h2r : (0 : ℝ) ≤ (2 * r - 1) * (2 * Real.sin t ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    have hexpand : M - 2 * Real.sin t ^ 2 =
        (1 - r) ^ 2 + (2 * r - 1) * (2 * Real.sin t ^ 2) := by
      rw [hMdef, hC2]
      ring
    linarith
  have hMpos : (0 : ℝ) < M := by
    have h2s : (0 : ℝ) < 2 * Real.sin t ^ 2 := by positivity
    linarith
  have hMhi : M ≤ 2 := by
    rw [hMdef]
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hM2sin : (0 : ℝ) < 2 * Real.sin t ^ 2 := by positivity
  have hratio_le : N / M ≤ 2 / Real.sin t ^ 2 := by
    have h1 : N / M ≤ 4 / M :=
      div_le_div_of_nonneg_right hNhi (le_of_lt hMpos)
    have h2 : (4 : ℝ) / M ≤ 4 / (2 * Real.sin t ^ 2) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) hMpos hM2sin]
      exact hMlo
    have h3 : (4 : ℝ) / (2 * Real.sin t ^ 2) = 2 / Real.sin t ^ 2 := by
      field_simp [ne_of_gt (pow_pos hsin 2), ne_of_gt hM2sin]
      ring
    rw [h3] at h2
    exact h1.trans h2
  have hratio_ge : (1 / 2 : ℝ) ≤ N / M := by
    have h1 : (1 : ℝ) / M ≤ N / M :=
      div_le_div_of_nonneg_right hNlo (le_of_lt hMpos)
    exact (one_div_le_one_div_of_le hMpos hMhi).trans h1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsin_nn : Real.log (Real.sin t) ≤ 0 :=
    Real.log_nonpos (le_of_lt hsin) hsin1
  have hupper : Real.log (N / M) / 2 ≤
      Real.log 2 - Real.log (Real.sin t) := by
    have hlog : Real.log (N / M) ≤ Real.log (2 / Real.sin t ^ 2) :=
      Real.log_le_log (div_pos hNpos hMpos) hratio_le
    have hexpand : Real.log (2 / Real.sin t ^ 2) =
        Real.log 2 - 2 * Real.log (Real.sin t) := by
      rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hsin 2)), Real.log_pow]
      ring
    rw [hexpand] at hlog
    linarith
  have hlower : -(Real.log 2 - Real.log (Real.sin t)) ≤
      Real.log (N / M) / 2 := by
    have hlog : Real.log (1 / 2) ≤ Real.log (N / M) :=
      Real.log_le_log (by norm_num) hratio_ge
    have hexpand : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [hexpand] at hlog
    linarith
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlower, hupper⟩

lemma ads_DrClosed_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun t : ℝ => adsDrClosed r t) := by
  have h : (fun t : ℝ => adsDrClosed r t) = adsDr r := by
    funext t
    exact (ads_Dr_eq_closed r t hr0 hr1).symm
  rw [h]
  exact ads_Dr_continuous r hr0 hr1

lemma ads_logSin_bound_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
      volume a b := by
  have hsin : IntervalIntegrable (Real.log ∘ Real.sin) volume a b :=
    intervalIntegrable_log_sin
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume a b :=
    intervalIntegrable_const
  simpa [Pi.sub_apply, Function.comp_apply] using hconst.sub hsin

lemma ads_SineSeries_eq_integral {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    adsSineSeries x = ∫ t in (0 : ℝ)..x, -Real.log (Real.tan t) := by
  rw [Set.mem_Icc] at hx
  have hSr_lim := ads_Sr_tendsto_SineSeries x
  have hSeqEq : (fun n : ℕ => adsSr (adsRho n) x) =
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, adsDrClosed (adsRho n) t) := by
    funext n
    exact ads_Sr_eq_integral (adsRho n) x (ads_Rho_nonneg n)
      (ads_Rho_lt_one n) hx.1
  rw [hSeqEq] at hSr_lim
  have hF_meas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun t : ℝ => adsDrClosed (adsRho n) t)
        (volume.restrict (Set.uIoc 0 x)) := by
    filter_upwards with n
    exact (ads_DrClosed_continuous (adsRho n) (ads_Rho_nonneg n)
      (ads_Rho_lt_one n)).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      ‖adsDrClosed (adsRho n) t‖ ≤
        Real.log 2 - Real.log (Real.sin t) := by
    filter_upwards [ads_Rho_eventually_ge] with n hn
    filter_upwards with t
    intro ht
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1, Set.mem_Ioc] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    exact ads_DrClosed_bound (adsRho n) t hn (le_of_lt (ads_Rho_lt_one n)) htIoc
  have hint := ads_logSin_bound_intervalIntegrable 0 x
  have hlim : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      Tendsto (fun n : ℕ => adsDrClosed (adsRho n) t) atTop
        (𝓝 (-Real.log (Real.tan t))) := by
    filter_upwards with t
    intro ht
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1, Set.mem_Ioc] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    exact ads_DrClosed_tendsto t htIoc
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
    hF_meas hbound hint hlim
  exact tendsto_nhds_unique hSr_lim hDCT

lemma ads_logTanIntegral_eq_neg_sineSeries {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    adsLogTanIntegral x = -adsSineSeries x := by
  have h := ads_SineSeries_eq_integral hx
  rw [intervalIntegral.integral_neg] at h
  unfold adsLogTanIntegral
  linarith

lemma ads_sin_odd_pi_div_two (k : ℕ) :
    Real.sin (((4 * k + 2 : ℕ) : ℝ) * (Real.pi / 4)) = (-1 : ℝ) ^ k := by
  have hcast : ((4 * k + 2 : ℕ) : ℝ) = 4 * (k : ℝ) + 2 := by
    push_cast
    ring
  have harg : (4 * (k : ℝ) + 2) * (Real.pi / 4) =
      Real.pi / 2 + (k : ℝ) * Real.pi := by ring
  rw [hcast, harg, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]

lemma ads_SineSeries_pi_div_four :
    adsSineSeries (Real.pi / 4) =
      ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold adsSineSeries adsSineTerm
  apply tsum_congr
  intro n
  have harg : 2 * ((2 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) =
      ((4 * n + 2 : ℕ) : ℝ) * (Real.pi / 4) := by
    push_cast
    ring
  rw [harg, ads_sin_odd_pi_div_two]
  norm_num

lemma ads_logTanIntegral_pi_div_four :
    adsLogTanIntegral (Real.pi / 4) =
      -(∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
  rw [ads_logTanIntegral_eq_neg_sineSeries
    (show Real.pi / 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 4) by
      exact ⟨by positivity, le_rfl⟩),
    ads_SineSeries_pi_div_four]

end
end Real.Calculus.ArcsinDivSinIntegral
