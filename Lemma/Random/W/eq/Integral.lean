import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`W θ f j y = ∫ z, Kf θ f j z ∂(stageK θ y)` (bridge past the `𝔼` sugar on `Model.W`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
-- given
  (θ : Θ)
  (j : ℕ)
  (y : S) :
-- imply
  M.W θ f j y = ∫ z, M.Kf θ f j z ∂(M.stageK θ y) := by
-- proof
  have : IsProbabilityMeasure (M.stageK θ y) := inferInstance
  have : PSpace (M.stageK θ y) (id : ℝ × S × A → ℝ × S × A) :=
    ⟨measurable_id.aemeasurable⟩
  change Expectation.ofRV (M.stageK θ y) id (M.Kf θ f j) = _
  simp only [Expectation.ofRV, expectation_real, Measure.map_id]


-- created on 2026-10-11
