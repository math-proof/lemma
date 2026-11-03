import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the action value `(x, u) ↦ Q0 θ γ x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
  [ReferenceMeasure A] [MeasurableSingletonClass A]
  {M : DensityModel Θ S A}
-- given
  (h : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (γ : ℝ)
  (hγ : γ ∈ Set.Ico 0 1)
  (hP : ∀ x, (M θ).real ((fun ω : ℕ → ℝ × S × A => (ω 0).2.1) ⁻¹' {x}) ≠ 0)
  (hQA : ∀ x u,
    (M θ).real
      (((fun ω : ℕ → ℝ × S × A => (ω 0).2.1) ⁻¹' {x}) ∩
        ((fun ω : ℕ → ℝ × S × A => (ω 0).2.2) ⁻¹' {u})) ≠ 0) :
-- imply
  Measurable (fun z : S × A => M.Q0 θ γ z.1 z.2) := by
-- proof
  have hEq : (fun z : S × A => M.Q0 θ γ z.1 z.2) =
      fun z => M.rkd z.1 z.2 + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans z) := by
    funext z
    exact Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
      (M := M) hγ θ z.1 z.2 hP (hQA z.1 z.2)
  rw [hEq]
  have := M.env.trans_markov
  apply (MeasurableRkd (M := M)).add (Measurable.const_mul _ γ)
  apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.V0 θ γ z.2)
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h θ γ).stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
-- updated on 2026-11-02
