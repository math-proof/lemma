import Def.Analysis.Calculus.Gradient.Operators.Part2
import Macro.Order.Sup
import Lemma.Random.Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
open MeasureTheory ProbabilityTheory Topology Filter PolicyGradient PolicyGradient.Model Random Set


/--
Derivative of the time-free state value on a reachable state:
`θ ↦ Vc θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ ∫ z, Kf θ (clip ·.1) k z ∂(stageK θ x)) θ`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S)
  (θ : Θ)
  (hP : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  HasFDerivAt (fun θ => M.Vc θ γ x)
    (∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ x)) θ) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hW := fun k => Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb (M := M) h₀ hC (StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) k x
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁c : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hc : ContinuousAt (fun θ' => (M θ').real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁c h₀ h₁ 0 x θ).continuousAt
  exact HasFDerivAt.congr_of_eventuallyEq
    (hasFDerivAt_tsum (Summable_MulPowMulAdd_1.of.In_Ico h₂ (Fintype.card A * Cp * |M.env.R|))
      (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
      (fun k θ => by
        rw [norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
        exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₂.1 k))
      (Summable_MulPowWRc.of.In_Ico (M := M) h₂ θ x) θ)
    (hc.eventually_ne hP |>.mono fun θ' hp =>
      Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₂ θ' x hp)


-- created on 2026-10-06
-- updated on 2026-10-26
