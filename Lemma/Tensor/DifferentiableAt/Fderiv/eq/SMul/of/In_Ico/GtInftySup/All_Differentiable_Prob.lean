import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Tensor.Differentiable_Vc.of.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
`θ ↦ Qc θ γ x u` is differentiable with derivative `γ • ∑ y, T(x, u, y) • fderiv ℝ (fun θ ↦ Vc θ γ y) θ`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S)
  (u : A)
  (θ : Θ) :
-- imply
  DifferentiableAt ℝ (fun θ => M.Qc θ γ x u) θ ∧
    fderiv ℝ (fun θ => M.Qc θ γ x u) θ = γ • ∑ y, M.T x u y • fderiv ℝ (fun θ => M.Vc θ γ y) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hs : DifferentiableAt ℝ (fun θ => ∑ y, M.T x u y * M.Vc θ γ y) θ :=
    DifferentiableAt.fun_sum fun y _ => ((Tensor.Differentiable_Vc.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ y) θ).const_mul _
  refine ⟨(hs.const_mul γ).const_add _, ?_⟩
  unfold Model.Qc
  rw [fderiv_const_add, fderiv_const_mul hs,
    fderiv_fun_sum fun y _ => ((Tensor.Differentiable_Vc.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ y) θ).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun y _ => fderiv_const_mul ((Tensor.Differentiable_Vc.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ y) θ) _


-- created on 2026-10-06
