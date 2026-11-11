import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
The state component of `stageK θ ∘ₘ ν` is distributed as `ν` (continuous-action model).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (ν : Measure 𝒮) :
-- imply
  (M.stageK θ ∘ₘ ν).map (fun z => z.2.1) = ν := by
-- proof
  have := M.env.reward_markov
  rw [Measure.map_comp _ _ (by fun_prop)]
  have h : (M.stageK θ).map (fun z => z.2.1) = Kernel.deterministic id measurable_id := by
    unfold DensityModel.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ (M.policy.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod (Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id) (M.policy.kernel θ ⊗ₖ M.env.reward)
  rw [h, Measure.deterministic_comp_eq_map, Measure.map_id]


-- created on 2026-10-20
