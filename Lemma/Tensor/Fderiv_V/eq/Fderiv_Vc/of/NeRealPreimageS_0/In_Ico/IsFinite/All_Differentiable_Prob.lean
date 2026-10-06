import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Tensor.V.eq.Vc.of.NeRealPreimageS_0.In_Ico.IsFinite.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
On a reachable state, the derivative of the state value equals that of its time-free closed form:
`fderiv ℝ (fun θ' ↦ V θ' γ t x) θ = fderiv ℝ (fun θ' ↦ Vc θ' γ x) θ`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t x) θ = fderiv ℝ (fun θ' => M.Vc θ' γ x) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  exact (Tensor.V.eq.Vc.of.NeRealPreimageS_0.In_Ico.IsFinite.All_Differentiable_Prob (M := M) h₀ h₁ h₂ t x θ h₃).fderiv_eq


-- created on 2026-10-06
