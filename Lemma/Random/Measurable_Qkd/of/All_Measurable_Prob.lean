import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the action value `(x, u) ↦ Q0 θ γ x u`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
-- given
  (h : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (hγ : γ ∈ Set.Ico 0 1)
  (hQA : ∀ x u,
    (M θ).real
      (((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω 0).2.1) ⁻¹' {x}) ∩
        ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω 0).2.2) ⁻¹' {u})) ≠ 0) :
-- imply
  Measurable (fun z : 𝒮 × 𝒜 => M.Q0 θ γ z.1 z.2) := by
-- proof
  have hEq : (fun z : 𝒮 × 𝒜 => M.Q0 θ γ z.1 z.2) =
      fun z => M.rkd z.1 z.2 + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans z) := by
    funext z
    exact Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
      (M := M) hγ (hQA z.1 z.2)
  rw [hEq]
  have := M.env.trans_markov
  apply (MeasurableRkd (M := M)).add (Measurable.const_mul _ γ)
  apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z => M.V0 θ γ z.2)
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h θ γ).stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
-- updated on 2026-11-13
