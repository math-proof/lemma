import Lemma.Random.Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob
import Lemma.Random.Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
gradient of the Bellman equation for the closed-form value function
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S)
  (θ : Θ) :
-- imply
  fderiv ℝ (fun θ => M.V0 θ γ x) θ =
    ∑ u, M.Qk θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ +
    γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ => M.V0 θ γ y) θ := by
-- proof
  have := M.env.trans_markov
  have hπm : ∀ θ u, Measurable (fun x : S => M.policy.prob θ x u) := fun _ _ =>
    measurable_of_finite _
  have hb : (fun θ => M.V0 θ γ x) = fun θ => ∑ u, M.policy.prob θ x u * M.Qk θ γ x u := by
    funext θ'
    change M.Vk θ' γ x = ∑ u, M.policy.prob θ' x u * M.Qk θ' γ x u
    exact Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob (M := M) hπm h₂ θ' x
  have hVdiff : ∀ y, DifferentiableAt ℝ (fun θ => M.V0 θ γ y) θ := fun y =>
    (Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₀ h₁ h₂ y) θ
  have hT : ∀ θ' u, ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u)) =
      ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ' γ y := fun θ' u => by
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul, mul_comm]
  have hQk_eq : ∀ u, (fun θ => M.Qk θ γ x u) =
      fun θ => M.rk x u + γ * ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ γ y := fun u => by
    funext θ'
    calc
      M.Qk θ' γ x u
          = M.rk x u + γ * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u)) := rfl
      _ = M.rk x u + γ * ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ' γ y := by
          rw [hT]
  have hQdiff : ∀ u, DifferentiableAt ℝ (fun θ => M.Qk θ γ x u) θ := fun u => by
    have hs : DifferentiableAt ℝ
        (fun θ => ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ γ y) θ :=
      DifferentiableAt.fun_sum fun y _ => (hVdiff y).const_mul _
    exact (hQk_eq u ▸ (hs.const_mul γ).const_add _)
  have hQf : ∀ u, fderiv ℝ (fun θ => M.Qk θ γ x u) θ =
      γ • ∑ y, (M.env.trans (x, u)).real {y} • fderiv ℝ (fun θ => M.V0 θ γ y) θ := by
    intro u
    have hs : DifferentiableAt ℝ
        (fun θ => ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ γ y) θ :=
      DifferentiableAt.fun_sum fun y _ => (hVdiff y).const_mul _
    rw [hQk_eq u, fderiv_const_add, fderiv_const_mul hs,
      fderiv_fun_sum fun y _ => (hVdiff y).const_mul _]
    simp [fderiv_const_mul (hVdiff _), Finset.smul_sum, smul_smul, smul_comm]
  rw [hb, fderiv_fun_sum fun u _ => ((h₀ x u) θ).fun_mul (hQdiff u)]
  simp_rw [fderiv_fun_mul ((h₀ _ _) θ) (hQdiff _), hQf]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  unfold Model.P1
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
  congr 1
  ring


-- created on 2026-10-06
-- updated on 2026-11-03
