import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
the gradients of the state-value function are bounded over the reachable pairs `(t, x)`:
by time-homogeneity (`Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob`)
the derivative of `V(t, x)` equals that of `Vc(x)`, and `S` is finite
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
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
  (θ : Θ) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => V θ p.1 p.2) θ‖) ''
    {p | (M θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
-- proof
  intro Vθ
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  refine ⟨∑ x, ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  beta_reduce
  dsimp only [Vθ]
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) p.1 p.2 θ h₀ h₁ h₂ h₃ hp]
  apply Finset.single_le_sum (f := fun x => ‖fderiv ℝ (fun θ => M.Vc θ γ x) θ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)


-- created on 2026-10-06
-- updated on 2026-10-10
