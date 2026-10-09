import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Real.NormIntegral.le.of.All_LeNormMul.EqIntegral_1
open MeasureTheory PolicyGradient Random Real


/--
The `k`-step expected reward with a density policy is bounded: `‖Wkd θ k x‖ = ‖𝔼[r[t+k] | s[t] = x]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (θ : Θ)
  (k : ℕ)
  (x : S) :
-- imply
  ‖M.Wkd θ k x‖ ≤ |M.env.R| := by
-- proof
  induction k generalizing x with
  | zero =>
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (M.pol.integral_eq_one θ x)
    intro u
    rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
    exact mul_le_mul_of_nonneg_left (NormRkd.le.Abs_R (M := M) x u) (M.pol.nonneg θ x u)
  | succ k ih =>
    have := M.env.trans_markov
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (M.pol.integral_eq_one θ x)
    intro u
    rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
    apply mul_le_mul_of_nonneg_left _ (M.pol.nonneg θ x u)
    simpa using norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall fun y => ih y)


-- created on 2026-10-07
