import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Lemma.Random.NormWk.le.Abs_R
open MeasureTheory PolicyGradient Random


/--
For `γ ∈ [0, 1)` the discounted series `∑ k, γ ^ k * Wk θ k x` is summable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  Summable (fun k => γ ^ k * M.Wk θ k x) := by
-- proof
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h.1 h.2).mul_right |M.env.R|) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
  apply mul_le_mul_of_nonneg_left (NormWk.le.Abs_R (M := M) θ k x) (pow_nonneg h.1 k)


-- created on 2026-10-07
