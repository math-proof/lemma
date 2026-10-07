import sympy.stats.policy_trajectory.continuous
import sympy.Basic
open MeasureTheory PolicyGradient


/--
The expected clamped reward is bounded: `‖rk x u‖ = ‖𝔼[r[t] | s[t] = x, a[t] = u]‖ ≤ |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (x : S)
  (u : A) :
-- imply
  ‖M.rk x u‖ ≤ |M.env.R| := by
-- proof
  have := M.env.reward_markov
  have h := norm_integral_le_of_norm_le_const (μ := M.env.reward (x, u))
    (f := fun ρ => max (-M.env.R) (min M.env.R ρ)) (C := |M.env.R|)
    (Filter.Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(neg_le_neg (le_abs_self _)).trans (le_max_left _ _),
        max_le (neg_le_abs _) ((min_le_left _ _).trans (le_abs_self _))⟩)
  simpa [Model.rk] using h


-- created on 2026-10-07
