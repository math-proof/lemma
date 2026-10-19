import sympy.stats.policy_trajectory.gradient
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`Pn θ n x y = ∫ z, Kf θ (1{y = s z}) n z ∂(stageK θ x)` (bridge past the `𝔼` sugar on `Model.Pn`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : S) :
-- imply
  M.Pn θ n x y =
    ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z ∂(M.stageK θ x) := by
-- proof
  unfold Model.Pn
  have : IsProbabilityMeasure (M.stageK θ x) := inferInstance
  have : PSpace (M.stageK θ x) (id : ℝ × S × A → ℝ × S × A) :=
    ⟨measurable_id.aemeasurable⟩
  change Expectation.ofRV (M.stageK θ x) id (M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n) = _
  simp only [Expectation.ofRV, expectation_real, Measure.map_id]


-- created on 2026-10-11
