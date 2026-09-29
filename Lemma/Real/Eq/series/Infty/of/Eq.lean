import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma coefficient
  {A B : ℕ → ℝ}
  {r : ℝ}
-- given
  (h₀ : 0 < r)
  (h₁ : ∀ x, |x| < r → Summable fun n => A n * x ^ n)
  (h₂ : ∀ x, |x| < r → Summable fun n => B n * x ^ n)
  (h : ∀ x, |x| < r → ∑' n, A n * x ^ n = ∑' n, B n * x ^ n) :
-- imply
  ∀ n, A n = B n := by
-- proof
  have rad : ∀ C : ℕ → ℝ, (∀ x, |x| < r → Summable fun n => C n * x ^ n) → 0 < (FormalMultilinearSeries.ofScalars ℝ C).radius := by
    intro C hC
    have hs : |r / 2| < r := by
      rw [abs_of_pos (by linarith)]
      linarith
    have ht := ((hC (r / 2) hs).tendsto_atTop_zero).norm
    simp only [norm_zero] at ht
    have hr : (0 : ℝ) ≤ r / 2 := by linarith
    have hle : (((r / 2).toNNReal : NNReal) : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℝ C).radius := by
      apply FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0)
      convert ht using 2 with n
      rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Real.coe_toNNReal _ hr, Real.norm_of_nonneg hr]
    refine lt_of_lt_of_le ?_ hle
    exact ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr (by linarith))
  have hsum : ∀ C : ℕ → ℝ, ∀ x, (FormalMultilinearSeries.ofScalars ℝ C).sum x = ∑' n, C n * x ^ n := by
    intro C x
    simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hA := ((FormalMultilinearSeries.ofScalars ℝ A).hasFPowerSeriesOnBall (rad A h₁)).hasFPowerSeriesAt
  have hB := ((FormalMultilinearSeries.ofScalars ℝ B).hasFPowerSeriesOnBall (rad B h₂)).hasFPowerSeriesAt
  have heq := hA.eq_formalMultilinearSeries_of_eventually hB (by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) h₀] with x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    rw [hsum, hsum, h x hx])
  intro n
  have hn := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => 1)) heq
  simpa [FormalMultilinearSeries.ofScalars_apply_eq] using hn


-- created on 2026-09-27
