import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.In_Ico
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
open MeasureTheory ProbabilityTheory Topology Filter PolicyGradient PolicyGradient.Model Random Set


/--
Derivative of the time-free closed-form state value: `θ ↦ Vc θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ ∫ z, Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(stageK θ x)) θ`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => M.Vc θ γ x) (∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ x)) θ) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hW := fun k => Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb (M := M) h₀ hC (StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) k x
  exact HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_tsum (Summable_MulPowMulAdd_1.of.In_Ico h₂ (Fintype.card A * Cp * |M.env.R|))
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
      exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₂.1 k))
    (Summable_MulPowWRc.of.In_Ico (M := M) h₂ θ x) θ) (EventuallyEq.of_eq (funext fun θ => Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) (γ := γ) θ x))


-- created on 2026-10-06
-- updated on 2026-10-12
