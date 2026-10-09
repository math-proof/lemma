import Mathlib
import sympy.Basic

open MeasureTheory Metric

/--
[AnalyticOnNhd_log_norm_le_circleAverage_log_norm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.lean)
-/
@[path]
private lemma main
  {F : ℂ → ℂ}
  {c : ℂ}
  {R : ℝ}
-- given
  (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|))
  (hc : F c ≠ 0) :
-- imply
  Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by
-- proof
  rcases eq_or_ne R 0 with rfl | hR
  · simp [Real.circleAverage_zero]
  rw [AnalyticOnNhd.circleAverage_log_norm hR hF hc]
  refine le_add_of_nonneg_left (finsum_nonneg fun u ↦ ?_)
  by_cases hu : u ∈ Metric.closedBall c |R|
  · refine mul_nonneg ?_ ?_
    · have h0 : (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.closedBall c |R|) u := by
        simpa using (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF) u
      exact_mod_cast h0
    · rcases eq_or_ne u c with rfl | huc
      · simp
      · have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
        rw [← Real.log_abs, abs_mul, abs_inv, abs_norm]
        refine Real.log_nonneg ?_
        rw [le_mul_inv_iff₀ hpos, one_mul]
        simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_closedBall.mp hu)
  · have : (MeromorphicOn.divisor F (Metric.closedBall c |R|)) u = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
    simp [this]


-- created on 2026-10-05
