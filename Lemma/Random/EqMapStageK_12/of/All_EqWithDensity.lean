import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The state component of `stageK θ ∘ₘ ν` is distributed as `ν` (continuous-action model).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (ν : Measure 𝒮) :
-- imply
  (M.stageK θ ∘ₘ ν).map (fun z => z.2.1) = ν := by
-- proof
  rw [Measure.map_comp _ _ (by fun_prop)]
  have h : (M.stageK θ).map (fun z => z.2.1) = Kernel.deterministic id measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod (Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id) (M.kernel θ ⊗ₖ M.rewardK)
  rw [h, Measure.deterministic_comp_eq_map, Measure.map_id]


-- created on 2026-10-20
-- updated on 2026-11-16
