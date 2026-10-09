import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
open MeasureTheory PolicyGradient Random Set


/--
For a differentiable policy with bounded gradient (measurable in the state), the closed-form state value on a general
state space has a bounded gradient: `sup[θ, y] ‖∇[θ] Vk θ γ y‖ < ∞`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (h₃ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u)) :
-- imply
  sup[θ, y] ‖∇[θ] M.Vk θ γ y‖ < ∞ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  refine ⟨∑' k : ℕ, γ ^ k * ((k + 1) * (Fintype.card A * Cp * |M.env.R|)), ?_⟩
  rintro _ ⟨⟨θ, y⟩, rfl⟩
  show ‖gradient (fun θ => M.Vk θ γ y) θ‖ ≤ _
  rw [gradient, LinearIsometryEquiv.norm_map,
    (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ y θ).fderiv]
  refine tsum_of_norm_bounded (Summable_MulPowMulAdd_1.of.In_Ico h₂ _).hasSum fun k => ?_
  rw [norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
  apply mul_le_mul_of_nonneg_left
    ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob (M := M) h₃ h₀ hC k y).2 θ)
    (pow_nonneg h₂.1 k)


-- created on 2026-10-07
