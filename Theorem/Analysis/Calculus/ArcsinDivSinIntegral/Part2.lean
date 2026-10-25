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
import Def.Analysis.Calculus.ArcsinDivSinIntegral.Part2
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

lemma ads_odd_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ))
      ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2) := by
  have h₁ := Complex.hasSum_taylorSeries_neg_log (z := z) hz
  have h₂ := Complex.hasSum_taylorSeries_neg_log (z := -z) (by simpa using hz)
  rw [show (1 : ℂ) - -z = 1 + z by ring] at h₂
  have hdiv := (h₁.sub h₂).div_const (2 : ℂ)
  have hval : (-Complex.log (1 - z) - -Complex.log (1 + z)) / 2 =
      (-Complex.log (1 - z) + Complex.log (1 + z)) / 2 := by ring
  rw [hval] at hdiv
  replace hdiv := (Nat.divModEquiv 2).symm.hasSum_iff.mpr hdiv
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply] at hdiv
  simp_rw [← mul_comm 2 _] at hdiv
  refine hdiv.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  have heven : Even (2 * k + 0) := ⟨k, by ring⟩
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  rw [heven.neg_pow, hodd.neg_pow]
  simp only [sub_self, zero_div, zero_add]
  rw [neg_div, sub_neg_eq_add, add_self_div_two]

lemma ads_polar_pow (r θ : ℝ) (n : ℕ) :
    ((((r * Real.cos θ : ℝ)) : ℂ) + (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) ^ n =
      ((((r ^ n * Real.cos ((n : ℝ) * θ) : ℝ)) : ℂ) +
        (((r ^ n * Real.sin ((n : ℝ) * θ) : ℝ)) : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : (((n + 1 : ℕ)) : ℝ) * θ = θ + (n : ℝ) * θ := by
      push_cast
      ring
    have hrpow : r ^ (n + 1) = r * r ^ n := pow_succ' r n
    rw [pow_succ, ih]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.cos_add]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.sin_add]
      ring

lemma ads_polar_norm (r θ : ℝ) (hr : 0 ≤ r) :
    ‖((((r * Real.cos θ : ℝ)) : ℂ) +
      (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I)‖ = r := by
  have hnormSq : Complex.normSq ((((r * Real.cos θ : ℝ)) : ℂ) +
      (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) = r ^ 2 := by
    rw [Complex.normSq_add_mul_I]
    have htrig := Real.cos_sq_add_sin_sq θ
    have hexpand : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  rw [Complex.norm_def, hnormSq, Real.sqrt_sq hr]

lemma ads_Dr_eq_closed (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    adsDr r x = adsDrClosed r x := by
  unfold adsDr adsDrClosed
  set θ : ℝ := 2 * x with hθ
  set z : ℂ := (((r * Real.cos θ : ℝ) : ℂ) +
    ((r * Real.sin θ : ℝ) : ℂ) * Complex.I) with hz
  have hnorm : ‖z‖ < 1 := by
    rw [hz, ads_polar_norm r θ hr0]
    exact hr1
  have hodd := ads_odd_hasSum hnorm
  have hre := Complex.hasSum_re hodd
  have hterm (k : ℕ) : (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re =
      r ^ (2 * k + 1) * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ) /
        ((2 * k + 1 : ℕ) : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, hz, ads_polar_pow]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero]
  have hdr : (fun k : ℕ => r ^ (2 * k + 1) * 2 *
      Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) / ((2 * k + 1 : ℕ) : ℝ)) =
      fun k : ℕ => 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re := by
    funext k
    rw [hterm k]
    have harg : ((2 * k + 1 : ℕ) : ℝ) * θ =
        2 * ((2 * k + 1 : ℕ) : ℝ) * x := by
      rw [hθ]
      ring
    rw [harg]
    ring
  have htsum : (∑' k : ℕ,
      2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re) =
      2 * ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re :=
    (hre.mul_left 2).tsum_eq
  rw [hdr, htsum]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    exact (lt_irrefl 1 hnorm)
  have hzn1 : z ≠ -1 := by
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  have hminus : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hplus : (1 : ℂ) + z ≠ 0 := by
    intro h
    apply hzn1
    linear_combination h
  have hplusForm : (1 : ℂ) + z =
      ((1 + r * Real.cos θ : ℝ) : ℂ) +
        ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [hz, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hminusForm : (1 : ℂ) - z =
      ((1 - r * Real.cos θ : ℝ) : ℂ) +
        ((-(r * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
    rw [hz, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have hnormPlus : Complex.normSq (1 + z) =
      1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [hplusForm, Complex.normSq_add_mul_I]
    have htrig := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 + r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        1 + 2 * r * Real.cos θ +
          r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  have hnormMinus : Complex.normSq (1 - z) =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [hminusForm, Complex.normSq_add_mul_I]
    have htrig := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 - r * Real.cos θ) ^ 2 + (-(r * Real.sin θ)) ^ 2 =
        1 - 2 * r * Real.cos θ +
          r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  have hplusPos : 0 < 1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hnormPlus]
    exact Complex.normSq_pos.mpr hplus
  have hminusPos : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hnormMinus]
    exact Complex.normSq_pos.mpr hminus
  have hreLog : ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re =
      (-Real.log ‖1 - z‖ + Real.log ‖1 + z‖) / 2 := by
    have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by simp
    rw [htwo, Complex.div_ofReal_re, Complex.add_re, Complex.neg_re,
      Complex.log_re, Complex.log_re]
  rw [hreLog]
  have eplus : Real.log ‖1 + z‖ =
      Real.log (1 + 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hnormPlus, Real.log_sqrt (le_of_lt hplusPos)]
  have eminus : Real.log ‖1 - z‖ =
      Real.log (1 - 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hnormMinus, Real.log_sqrt (le_of_lt hminusPos)]
  rw [eplus, eminus,
    Real.log_div (ne_of_gt hplusPos) (ne_of_gt hminusPos)]
  ring

lemma ads_Sr_norm_le (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    ‖r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)‖ ≤
      (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  have hden : (0 : ℝ) < (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hden]
  have hrabs : |r| ≤ 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hrpow : |r| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hrabs
  have hsin := Real.abs_sin_le_one (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
  have hnum : |r ^ (2 * k + 1) *
      Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)| ≤ 1 := by
    rw [abs_mul, abs_pow]
    calc
      |r| ^ (2 * k + 1) * |Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)| ≤
          1 * 1 := mul_le_mul hrpow hsin (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)

lemma ads_Sr_summable (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Summable (fun k : ℕ => r ^ (2 * k + 1) *
      Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => ads_Sr_norm_le r x hr0 hr1 k) ads_base_summable

lemma ads_Sr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Continuous (adsSr r) := by
  apply continuous_tsum (fun n => ?_) ads_base_summable
    (fun n x => ads_Sr_norm_le r x hr0 hr1 n)
  have hlin : Continuous (fun x : ℝ => 2 * ((2 * n + 1 : ℕ) : ℝ) * x) := by
    fun_prop
  apply Continuous.div_const
  exact continuous_const.mul (Real.continuous_sin.comp hlin)

lemma ads_Dr_norm_le (r z : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
        ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n := by
  have hden : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  have hden_pos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by linarith
  have hrpow : r ^ (2 * n + 1) ≤ (r ^ 2) ^ n := by
    have hexp : r ^ (2 * n + 1) = r * (r ^ 2) ^ n := by
      rw [pow_succ', pow_mul]
    rw [hexp]
    calc
      r * (r ^ 2) ^ n ≤ 1 * (r ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right (le_of_lt hr1) (by positivity)
      _ = (r ^ 2) ^ n := one_mul _
  have hcos := Real.abs_cos_le_one (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
  have hnum : |r ^ (2 * n + 1) * 2 *
      Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| ≤ 2 * (r ^ 2) ^ n := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0 _),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      r ^ (2 * n + 1) * 2 * |Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| ≤
          (r ^ 2) ^ n * 2 * 1 := by
        apply mul_le_mul _ hcos (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hrpow (by norm_num)
      _ = 2 * (r ^ 2) ^ n := by ring
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hden_pos]
  calc
    |r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| /
        ((2 * n + 1 : ℕ) : ℝ) ≤
        (2 * (r ^ 2) ^ n) / ((2 * n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    _ ≤ 2 * (r ^ 2) ^ n := div_le_self (by positivity) hden

lemma ads_Sr_term_hasDerivAt (r x : ℝ) (k : ℕ) :
    HasDerivAt
      (fun y : ℝ => r ^ (2 * k + 1) *
        Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * y) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        ((2 * k + 1 : ℕ) : ℝ)) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * ((2 * k + 1 : ℕ) : ℝ) * y)
      (2 * ((2 * k + 1 : ℕ) : ℝ)) x := by
    simpa using (hasDerivAt_id' x).const_mul (2 * ((2 * k + 1 : ℕ) : ℝ))
  have hsin := (Real.hasDerivAt_sin
    (2 * ((2 * k + 1 : ℕ) : ℝ) * x)).comp x hlin
  have hdiv := (hsin.const_mul (r ^ (2 * k + 1))).div_const
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hsimp : r ^ (2 * k + 1) *
        (Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) *
          (2 * ((2 * k + 1 : ℕ) : ℝ))) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2) =
      r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        ((2 * k + 1 : ℕ) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

lemma ads_Sr_hasDerivAt (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (adsSr r) (adsDr r x) x := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left 2
  have hderiv : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivAt
        (fun y : ℝ => r ^ (2 * n + 1) *
          Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * y) /
            (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        (r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
          ((2 * n + 1 : ℕ) : ℝ)) z :=
    fun n z _ => ads_Sr_term_hasDerivAt r z n
  have hbound : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
          ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n :=
    fun n z _ => ads_Dr_norm_le r z hr0 hr1 n
  have hsum0 : Summable (fun n : ℕ => r ^ (2 * n + 1) *
      Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * 0) /
        (((2 * n + 1 : ℕ) : ℝ) ^ 2)) := by
    simp
  have h := hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_univ
    isPreconnected_univ hderiv hbound (Set.mem_univ 0) hsum0 (Set.mem_univ x)
  unfold adsSr adsDr at ⊢
  exact h

lemma ads_Dr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (adsDr r) := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left 2
  apply continuous_tsum (fun n => ?_) hmajorant
    (fun n x => ads_Dr_norm_le r x hr0 hr1 n)
  have hlin : Continuous (fun x : ℝ => 2 * ((2 * n + 1 : ℕ) : ℝ) * x) := by
    fun_prop
  apply Continuous.div_const
  exact continuous_const.mul (Real.continuous_cos.comp hlin)

lemma ads_Sr_zero (r : ℝ) : adsSr r 0 = 0 := by
  unfold adsSr
  simp

lemma ads_Sr_eq_integral (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) :
    adsSr r x = ∫ t in (0 : ℝ)..x, adsDrClosed r t := by
  have hSrC : ContinuousOn (adsSr r) (Set.Icc 0 x) :=
    (ads_Sr_continuous r hr0 (le_of_lt hr1)).continuousOn
  have hFTC : (∫ t in (0 : ℝ)..x, adsDr r t) = adsSr r x - adsSr r 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hSrC
      (fun t _ => ads_Sr_hasDerivAt r t hr0 hr1)
      (((ads_Dr_continuous r hr0 hr1).continuousOn.mono
        (Set.subset_univ _)).intervalIntegrable_of_Icc hx0)
  rw [ads_Sr_zero, sub_zero] at hFTC
  have heq : (∫ t in (0 : ℝ)..x, adsDr r t) =
      ∫ t in (0 : ℝ)..x, adsDrClosed r t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact ads_Dr_eq_closed r t hr0 hr1
  rw [heq] at hFTC
  exact hFTC.symm

end
end Real.Calculus.ArcsinDivSinIntegral
