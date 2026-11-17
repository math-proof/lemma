import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory PolicyGradient


/--
The expected clamped reward is bounded: `‖rkd x u‖ = ‖𝔼[r[t] | s[t] = x, a[t] = u]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ‖M.rkd sₜ aₜ‖ ≤ |M.R| := by
-- proof
  have h := norm_integral_le_of_norm_le_const (μ := M.reward (sₜ, aₜ))
    (f := fun ρ => clip ρ (-M.R) M.R) (C := |M.R|)
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
  simpa [Model.rkd] using h


-- created on 2026-10-07
-- updated on 2026-11-16