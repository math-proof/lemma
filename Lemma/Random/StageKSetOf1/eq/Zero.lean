import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The stage kernel of the trajectory model `M` puts no mass on rewards outside `[-R, R]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (y : S) :
-- imply
  M.stageK θ y {z | z.1 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
-- proof
  have hs : MeasurableSet {z : S × A × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_snd.snd
  have := M.env.reward_markov
  unfold Model.stageK
  have hs' : MeasurableSet {z : ℝ × S × A | z.1 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_fst
  rw [Kernel.map_apply' _ (by fun_prop) _ hs']
  show M.stageK₀ θ y {z : S × A × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} = 0
  unfold Model.stageK₀
  rw [Kernel.prod_apply, Kernel.deterministic_apply, id, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hs, Kernel.compProd_apply (measurable_prodMk_left hs)]
  have h : ∀ b, M.env.reward (y, b) (Prod.mk b ⁻¹' (Prod.mk y ⁻¹'
      {z : S × A × ℝ | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R})) = 0 := fun b => M.env.reward_bdd (y, b)
  simp only [h, lintegral_zero]


-- created on 2026-10-07
