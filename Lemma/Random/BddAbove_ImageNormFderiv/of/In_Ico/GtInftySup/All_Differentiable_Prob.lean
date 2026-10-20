import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
the gradients of the state-value function are bounded over the reachable pairs `(t, x)`:
by time-homogeneity (`Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob`)
the derivative of `V(t, x)` equals that of `Vc(x)`, and `S` is finite
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (θ : Θ)
  (h₅ : ∀ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => M.V θ γ p.1 p.2) θ‖) ''
    {p | (M θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  refine ⟨∑ x, ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  beta_reduce
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) p.1 p.2 θ h₀ h₁ h₂ h₃ hp (h₅ p.2)]
  apply Finset.single_le_sum (f := fun x => ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)


-- created on 2026-10-06
-- updated on 2026-10-20
