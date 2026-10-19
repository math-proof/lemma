import Lemma.Random.Vc.eq.Sum_MulProbQc.of.In_Ico
import Lemma.Random.DifferentiableAt.EqFderiv_FunQc_SMulSum_SMulTFderivVc.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
gradient of the Bellman equation for the closed-form value function
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
  (x : S)
  (θ : Θ) :
-- imply
  fderiv ℝ (fun θ => M.Vc θ γ x) θ =
    ∑ u, M.Qc θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ +
    γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ => M.Vc θ γ y) θ := by
-- proof
  have hQ := fun u => DifferentiableAt.EqFderiv_FunQc_SMulSum_SMulTFderivVc.of.In_Ico.GtInftySup_Norm.All_All_Differentiable_FunProbPol (M := M) h₀ h₁ h₂ x u θ
  rw [funext fun θ => Vc.eq.Sum_MulProbQc.of.In_Ico (M := M) h₂ θ x, fderiv_fun_sum fun u _ => ((h₀ x u) θ).fun_mul (hQ u).1]
  simp_rw [fderiv_fun_mul ((h₀ _ _) θ) (hQ _).1, (hQ _).2]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  unfold Model.P1
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
  congr 1
  ring


-- created on 2026-10-06
