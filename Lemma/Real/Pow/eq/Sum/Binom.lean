import Mathlib.Analysis.Analytic.Binomial
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x r : ℝ}
-- given
  (h : |x| < 1) :
-- imply
  (x + 1) ^ r = ∑' n, Ring.choose r n * x ^ n := by
-- proof
  have hx : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_lt_one.mpr h
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := r)).hasSum hx
  rw [zero_add] at hs
  rw [add_comm x 1, ← hs.tsum_eq]
  congr 1
  funext n
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]


-- created on 2020-10-20
