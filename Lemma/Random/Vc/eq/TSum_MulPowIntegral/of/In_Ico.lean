import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`Vc θ γ y = ∑' k, γ ^ k * ∫ z, Kf θ rc k z ∂(stageK θ y)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (y : S) :
-- imply
  let rc (z : ℝ × S × A) : ℝ := clip z.1 (-M.env.R) M.env.R
  M.Vc θ γ y = ∑' k, γ ^ k * ∫ z, M.Kf θ rc k z ∂(M.stageK θ y) := by
-- proof
  intro rc
  unfold Model.Vc
  refine tsum_congr fun k => ?_
  dsimp only
  congr 1
  simp only [Expectation.ofRV, expectation_real, Expectation.asRV_function, Measure.map_id, rc]


-- created on 2026-10-11
