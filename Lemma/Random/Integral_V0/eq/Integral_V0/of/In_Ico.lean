import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Kernel


/-- The stage kernel `stageK θ y` is supported on the state `y`. -/
private lemma integral_V0_stageK
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  ∫ z, M.V0 θ γ z.2.1 ∂(M.stageK θ y) = M.V0 θ γ y := by
-- proof
  have hV0 : Measurable (M.V0 θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M)
      (fun θ => hStoch.measurable_π θ) θ γ
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    apply Kernel.fst_prod
  rw [← integral_map measurable_snd.fst.aemeasurable hV0.aestronglyMeasurable]
  rw [← Kernel.map_apply (M.stageK θ) (f := fun z : ℝ × 𝒮 × 𝒜 => z.2.1)
    (hf := measurable_snd.fst)]
  rw [hsk, Kernel.deterministic_apply]
  apply integral_dirac' _ y hV0.stronglyMeasurable

/--
Integrating a function of the next state against `stageK θ ∘ₘ trans` is integrating it against the transition.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (w : ℝ × 𝒮 × 𝒜) :
-- imply
  ∫ z, M.V0 θ γ z.2.1 ∂((M.trans w.2).toMeasure.bind (M.stageK θ)) =
    ∫ y, M.V0 θ γ y ∂(M.trans w.2) := by
-- proof
  have hV0 : Measurable (M.V0 θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M)
      (fun θ => hStoch.measurable_π θ) θ γ
  have hg : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1 :=
    (hV0.comp measurable_snd.fst).stronglyMeasurable
  have hV0b : ∀ y, ‖M.V0 θ γ y‖ ≤ (1 - γ)⁻¹ * |M.R| :=
    fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h θ y
  have hint : Integrable (fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1)
      ((M.trans w.2).toMeasure.bind (M.stageK θ)) :=
    Integrable.of_bound hg.aestronglyMeasurable ((1 - γ)⁻¹ * |M.R|)
      (Filter.Eventually.of_forall fun z => hV0b z.2.1)
  rw [Integral.eq.Integral_Integral.of.Integrable_Bind (κ := M.stageK θ)
    (μ := (M.trans w.2 : Measure 𝒮)) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  apply integral_V0_stageK (M := M) θ y


-- created on 2026-11-17
-- updated on 2026-11-17
