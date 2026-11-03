import Lemma.Random.HasFDerivAt_FunVc_TSum_SMulPowFderiv_FunW.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
For a differentiable policy with bounded gradient, `θ ↦ V0 θ γ x` is differentiable on every state.
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
  (x : S) :
-- imply
  Differentiable ℝ (fun θ => M.V0 θ γ x) := by
-- proof
  exact fun θ =>
    (Random.HasFDerivAt_FunVc_TSum_SMulPowFderiv_FunW.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol
      (M := M) h₀ h₁ h₂ x θ).differentiableAt


-- created on 2026-10-06
-- updated on 2026-11-03
