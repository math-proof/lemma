import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.NormW.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` the discounted series `∑ k, γ ^ k * W θ rc k y` is summable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : S) :
-- imply
  Summable (fun k => γ ^ k * M.W θ M.rc k y) := by
-- proof
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|) ?_
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (NormW.le.Abs_R (M := M) θ k y) (pow_nonneg hγ.1 k)


-- created on 2026-10-07
