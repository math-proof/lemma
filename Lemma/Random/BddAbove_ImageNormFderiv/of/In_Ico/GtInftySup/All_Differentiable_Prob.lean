import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
the gradients of the state-value function are bounded over the reachable pairs `(t, x)`:
by time-homogeneity (`Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob`)
the derivative of `V(t, x)` equals that of `Vc(x)`, and `S` is finite
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
  (θ : Θ) :
-- imply
  BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => M.V θ γ p.1 p.2) θ‖) ''
    {p | (M θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  refine ⟨∑ x, ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  beta_reduce
  rw [Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ p.1 p.2 θ hp]
  apply Finset.single_le_sum (f := fun x => ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)


-- created on 2026-10-06
