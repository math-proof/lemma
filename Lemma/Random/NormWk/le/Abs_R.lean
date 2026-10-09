import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Lemma.Random.NormRk.le.Abs_R
open MeasureTheory PolicyGradient Random


/--
The `k`-step expected reward on a general state space is bounded: `‖Wk θ k x‖ = ‖𝔼[r[t+k] | s[t] = x]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (k : ℕ)
  (x : S) :
-- imply
  ‖M.Wk θ k x‖ ≤ |M.env.R| := by
-- proof
  have hπ : ∀ x {g : A → ℝ} {C : ℝ}, (∀ u, ‖g u‖ ≤ C) → ‖∑ u, M.pol.prob θ x u * g u‖ ≤ C := fun x g C h =>
    calc _ ≤ ∑ u, ‖M.pol.prob θ x u * g u‖ := norm_sum_le _ _
      _ ≤ ∑ u, M.pol.prob θ x u * C := Finset.sum_le_sum fun u _ => by
          rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
          exact mul_le_mul_of_nonneg_left (h u) (M.pol.nonneg θ x u)
      _ = C := by rw [← Finset.sum_mul, M.pol.sum_eq_one, one_mul]
  induction k generalizing x with
  | zero =>
    apply hπ x fun u => NormRk.le.Abs_R (M := M) x u
  | succ k ih =>
    have := M.env.trans_markov
    apply hπ x
    intro u
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall fun y => ih y)
    simpa using h


-- created on 2026-10-07
