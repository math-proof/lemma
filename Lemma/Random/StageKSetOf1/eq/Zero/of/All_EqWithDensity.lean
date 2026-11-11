import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
The stage kernel of the continuous-action trajectory model `M` puts no mass on rewards outside `[-R, R]`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  M.stageK θ y {z | z.1 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
-- proof
  have hs : MeasurableSet {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_snd.snd
  have := M.env.reward_markov
  unfold DensityModel.stageK
  have hs' : MeasurableSet {z : ℝ × 𝒮 × 𝒜 | z.1 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_fst
  rw [Kernel.map_apply' _ (by fun_prop) _ hs']
  show (Kernel.deterministic id measurable_id ×ₖ (M.policy.kernel θ ⊗ₖ M.env.reward)) y
    {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} = 0
  rw [Kernel.prod_apply, Kernel.deterministic_apply, id, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hs, Kernel.compProd_apply (measurable_prodMk_left hs)]
  have h : ∀ b, M.env.reward (y, b) (Prod.mk b ⁻¹' (Prod.mk y ⁻¹'
      {z : 𝒮 × 𝒜 × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R})) = 0 := fun b => M.env.reward_bdd (y, b)
  simp only [h, lintegral_zero]


-- created on 2026-10-20
