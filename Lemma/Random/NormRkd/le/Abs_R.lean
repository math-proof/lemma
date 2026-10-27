import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
open MeasureTheory PolicyGradient


/--
The expected clamped reward is bounded: `‖rkd x u‖ = ‖𝔼[r[t] | s[t] = x, a[t] = u]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (x : S)
  (u : A) :
-- imply
  ‖M.rkd x u‖ ≤ |M.env.R| := by
-- proof
  have := M.env.reward_markov
  have h := norm_integral_le_of_norm_le_const (μ := M.env.reward (x, u))
    (f := fun ρ => clip ρ (-M.env.R) M.env.R) (C := |M.env.R|)
    (Filter.Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_le, clip]
      constructor
      ·
        apply le_min
        ·
          apply (neg_le_neg (le_abs_self _)).trans
          apply le_max_right
        ·
          apply neg_abs_le
      ·
        apply (min_le_right _ _).trans
        apply le_abs_self)
  simpa [DensityModel.rkd] using h


-- created on 2026-10-07
-- updated on 2026-10-26
