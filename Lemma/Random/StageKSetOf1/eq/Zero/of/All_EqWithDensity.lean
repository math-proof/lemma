import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The stage kernel of the continuous-action trajectory model `M` puts no mass on rewards outside `[-R, R]`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  M.stageK θ y {z | z.1 ∉ Set.Icc (-M.R) M.R} = 0 := by
-- proof
  have hs : MeasurableSet {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.R) M.R} :=
    (measurableSet_Icc.compl).preimage measurable_snd.snd
  unfold Model.stageK
  have hs' : MeasurableSet {z : ℝ × 𝒮 × 𝒜 | z.1 ∉ Set.Icc (-M.R) M.R} :=
    (measurableSet_Icc.compl).preimage measurable_fst
  rw [Kernel.map_apply' _ (by fun_prop) _ hs']
  show (Kernel.deterministic id measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)) y
    {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.R) M.R} = 0
  rw [Kernel.prod_apply, Kernel.deterministic_apply, id, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hs, Kernel.compProd_apply (measurable_prodMk_left hs)]
  have h : ∀ b, (M.reward (y, b) : Measure ℝ) (Prod.mk b ⁻¹' (Prod.mk y ⁻¹'
      {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.R) M.R})) = 0 := by
    intro b
    have hset :
      Prod.mk b ⁻¹' (Prod.mk y ⁻¹'
        {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.R) M.R}) =
        (Set.Icc (-M.R) M.R)ᶜ := by
      ext ρ
      simp
    rw [hset, measure_compl measurableSet_Icc (measure_ne_top _ _), measure_univ,
      M.reward_bdd (y, b), tsub_self]
  apply Eq.trans _ (lintegral_zero (μ := (M.kernel θ) y))
  apply lintegral_congr
  intro b
  simpa [Model.rewardK] using h b


-- created on 2026-10-20
-- updated on 2026-11-17