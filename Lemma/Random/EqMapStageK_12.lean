import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The state component of `stageK θ ∘ₘ ν` is distributed as `ν`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (ν : Measure S) :
-- imply
  (M.stageK θ ∘ₘ ν).map (fun z => z.2.1) = ν := by
-- proof
  have := M.env.reward_markov
  rw [Measure.map_comp _ _ (by fun_prop)]
  have h : (M.stageK θ).map (fun z => z.2.1) = Kernel.deterministic id measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ (M.pol.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod (Kernel.deterministic (id : S → S) measurable_id) (M.pol.kernel θ ⊗ₖ M.env.reward)
  rw [h, Measure.deterministic_comp_eq_map, Measure.map_id]


-- created on 2026-10-07
