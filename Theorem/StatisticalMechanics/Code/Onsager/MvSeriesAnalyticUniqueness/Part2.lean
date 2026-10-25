/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Def.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness


namespace StatMech.Onsager

open BigOperators

open Filter

theorem ons_summable_degreeFiberNorm
    {E : Type*}
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsum : ons_MvSeriesEvalSummable series weight) :
    Summable (ons_degreeFiberNorm series weight) := by
  let term : (E →₀ ℕ) → ℝ := fun m ↦
    ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖
  have hfiber := hsum.hasSum.tsum_fiberwise Finsupp.degree
  simpa only [ons_degreeFiberNorm, term] using hfiber.summable

theorem ons_norm_degreeFiberCoeff_le
    {E : Type*}
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsum : ons_MvSeriesEvalSummable series weight) (n : ℕ) :
    ‖ons_degreeFiberCoeff series weight n‖ ≤
      ons_degreeFiberNorm series weight n := by
  unfold ons_degreeFiberCoeff ons_degreeFiberNorm
  apply norm_tsum_le_tsum_norm
  exact hsum.subtype _

theorem ons_summable_norm_degreeFiberCoeff
    {E : Type*}
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsum : ons_MvSeriesEvalSummable series weight) :
    Summable fun n ↦ ‖ons_degreeFiberCoeff series weight n‖ := by
  exact Summable.of_nonneg_of_le
    (fun n ↦ norm_nonneg _)
    (ons_norm_degreeFiberCoeff_le series weight hsum)
    (ons_summable_degreeFiberNorm series weight hsum)

theorem ons_mvSeriesEval_smul_eq_degreeFiber
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsum : ons_MvSeriesEvalSummable series weight)
    (s : ℂ) (hs : ‖s‖ ≤ 1) :
    ons_mvSeriesEval series (fun e ↦ s * weight e) =
      ∑' n, ons_degreeFiberCoeff series weight n * s ^ n := by
  let scaledTerm : (E →₀ ℕ) → ℂ := fun m ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (fun e ↦ s * weight e) m
  have hscaledNorm : ∀ m,
      ‖scaledTerm m‖ ≤
        ‖MvPowerSeries.coeff m series *
          ons_mvMonomialValue weight m‖ := by
    intro m
    simp only [scaledTerm, ons_mvMonomialValue_smul, norm_mul, norm_pow]
    have hpow : ‖s‖ ^ Finsupp.degree m ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) hs
    calc
      ‖MvPowerSeries.coeff m series‖ *
          (‖s‖ ^ Finsupp.degree m * ‖ons_mvMonomialValue weight m‖) ≤
        ‖MvPowerSeries.coeff m series‖ *
          (1 * ‖ons_mvMonomialValue weight m‖) := by gcongr
      _ = _ := by ring
  have hscaled : Summable scaledTerm := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _)
      hscaledNorm hsum
  have hfiber := hscaled.hasSum.tsum_fiberwise Finsupp.degree
  symm
  calc
    (∑' n, ons_degreeFiberCoeff series weight n * s ^ n) =
        ∑' n, ∑' m : {m : E →₀ ℕ // Finsupp.degree m = n},
          scaledTerm m.1 := by
      apply tsum_congr
      intro n
      unfold ons_degreeFiberCoeff
      rw [← tsum_mul_right]
      apply tsum_congr
      intro m
      simp only [scaledTerm, ons_mvMonomialValue_smul, m.2]
      ring
    _ = ons_mvSeriesEval series (fun e ↦ s * weight e) := by
      exact hfiber.tsum_eq

theorem ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsum : ons_MvSeriesEvalSummable series weight)
    (hzero : ∀ᶠ s : ℂ in nhds 0,
      ons_mvSeriesEval series (fun e ↦ s * weight e) = 0)
    (n : ℕ) :
    ons_degreeFiberCoeff series weight n = 0 := by
  let c : ℕ → ℂ := ons_degreeFiberCoeff series weight
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ c
  have hcsum : Summable fun n ↦ ‖c n‖ := by
    simpa only [c] using
      ons_summable_norm_degreeFiberCoeff series weight hsum
  have hradius : (1 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    convert hcsum using 1 <;>
      simp [p, FormalMultilinearSeries.ofScalars_norm]
  have hradiusPos : 0 < p.radius :=
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hradius
  have hp : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hradiusPos).hasFPowerSeriesAt
  have heval : ∀ᶠ s : ℂ in nhds 0,
      p.sum s = ons_mvSeriesEval series (fun e ↦ s * weight e) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1)] with s hs
    have hs' : ‖s‖ ≤ 1 := by
      have : ‖s‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hs
      exact this.le
    change FormalMultilinearSeries.ofScalarsSum c s = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp only [smul_eq_mul, p, c]
    exact (ons_mvSeriesEval_smul_eq_degreeFiber
      series weight hsum s hs').symm
  have hpzero : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    apply hp.congr
    filter_upwards [heval, hzero] with s heq hz
    rw [heq, hz]
    rfl
  have hpSeries : p = 0 := hpzero.eq_zero
  have hc : c = 0 := by
    change FormalMultilinearSeries.ofScalars ℂ c = 0 at hpSeries
    rwa [FormalMultilinearSeries.ofScalars_series_eq_zero] at hpSeries
  exact congrFun hc n

end StatMech.Onsager
