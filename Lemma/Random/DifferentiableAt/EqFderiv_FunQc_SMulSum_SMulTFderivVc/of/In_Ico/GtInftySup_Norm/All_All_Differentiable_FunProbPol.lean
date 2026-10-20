import Lemma.Random.Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb
import Lemma.Random.Qc.eq.AddIntegral_RcMul_Sum_MulRealVc.of.NeMulRealPreimageSProb_0.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`θ ↦ Qc θ γ x u` is differentiable with derivative `γ • ∑ y, T(x, u, y) • fderiv ℝ (fun θ ↦ Vc θ γ y) θ`.
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
  (u : A)
  (θ : Θ)
  (hP : ∀ θ y, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0)
  (hπ : ∀ θ, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) * M.policy.prob θ x u ≠ 0) :
-- imply
  DifferentiableAt ℝ (fun θ => M.Qc θ γ x u) θ ∧
    fderiv ℝ (fun θ => M.Qc θ γ x u) θ = γ • ∑ y, (M.env.trans (x, u)).real {y} • fderiv ℝ (fun θ => M.Vc θ γ y) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have := M.env.trans_markov
  have := M.env.reward_markov
  have hQc : (fun θ => M.Qc θ γ x u) = fun θ =>
      (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
        γ * ∑ y, (M.env.trans (x, u)).real {y} * M.Vc θ γ y := by
    funext θ'
    exact Qc.eq.AddIntegral_RcMul_Sum_MulRealVc.of.NeMulRealPreimageSProb_0.In_Ico
      (M := M) θ' x u h₂ (hπ θ') (fun y _ => hP θ' y)
  have hs : DifferentiableAt ℝ (fun θ => ∑ y, (M.env.trans (x, u)).real {y} * M.Vc θ γ y) θ :=
    DifferentiableAt.fun_sum fun y _ =>
      ((Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₀ h₁ h₂ y
        (fun θ => hP θ y)) θ).const_mul _
  rw [hQc]
  refine ⟨(hs.const_mul γ).const_add _, ?_⟩
  rw [fderiv_const_add, fderiv_const_mul hs,
    fderiv_fun_sum fun y _ =>
      ((Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₀ h₁ h₂ y
        (fun θ => hP θ y)) θ).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun y _ =>
    fderiv_const_mul
      ((Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb (M := M) h₀ h₁ h₂ y
        (fun θ => hP θ y)) θ) _


-- created on 2026-10-06
-- updated on 2026-10-20
