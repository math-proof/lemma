import sympy.stats.policy_trajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`Kf θ f (j + 1) z = ∫ w, Kf θ f j w ∂(K θ z)` (bridge past the `𝔼` sugar on `Model.Kf`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
-- given
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × S × A) :
-- imply
  M.Kf θ f (j + 1) z = ∫ w, M.Kf θ f j w ∂(M.K θ z) := by
-- proof
  have : IsProbabilityMeasure (M.K θ z) := inferInstance
  have : PSpace (M.K θ z) (id : ℝ × S × A → ℝ × S × A) :=
    ⟨measurable_id.aemeasurable⟩
  change Expectation.ofRV (M.K θ z) id (M.Kf θ f j) = _
  simp only [Expectation.ofRV, expectation_real, Measure.map_id]


-- created on 2026-10-11
