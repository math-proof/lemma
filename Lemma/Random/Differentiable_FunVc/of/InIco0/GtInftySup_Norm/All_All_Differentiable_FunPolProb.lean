import Lemma.Random.HasFDerivAt_FunVc_TSum_SMulPowFderiv_FunW.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
For a differentiable policy with bounded gradient, `θ ↦ Vc θ γ x` is differentiable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S) :
-- imply
  Differentiable ℝ (fun θ => M.Vc θ γ x) := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  exact fun θ => (Random.HasFDerivAt_FunVc_TSum_SMulPowFderiv_FunW.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol (M := M) h₀ h₁ h₂ x θ).differentiableAt


-- created on 2026-10-06
