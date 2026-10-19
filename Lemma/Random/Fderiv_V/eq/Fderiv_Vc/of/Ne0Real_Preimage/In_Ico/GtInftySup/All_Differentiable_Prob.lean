import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state, the derivative of the state value equals that of its time-free closed form:
`fderiv ℝ (fun θ' ↦ V θ' γ t x) θ = fderiv ℝ (fun θ' ↦ Vc θ' γ x) θ`.
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
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let Vθ (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  fderiv ℝ (fun θ' => Vθ θ' t x) θ = fderiv ℝ (fun θ' => M.Vc θ' γ x) θ := by
-- proof
  intro Vθ
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  apply (V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) t x θ h₀ h₁ h₂ h₃ h₄).fderiv_eq


-- created on 2026-10-06
-- updated on 2026-10-10
