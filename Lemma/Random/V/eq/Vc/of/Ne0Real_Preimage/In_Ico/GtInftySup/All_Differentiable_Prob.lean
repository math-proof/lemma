import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`ℙ(s[t] = x) ≠ 0` and `ℙ(s[0] = x) ≠ 0` at `θ`), near `θ`:
`M.V θ' γ t x = M.Vc θ' γ x`.
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
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (h₅ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  (fun θ' => M.V θ' γ t x) =ᶠ[𝓝 θ] fun θ' => M.Vc θ' γ x := by
-- proof
  have hs : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  have h4' : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1) ⁻¹' {x}) ≠ 0 := by
    simpa [hs] using h₄
  have hc_t : ContinuousAt (fun θ' => (M θ').real ((fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1) ⁻¹' {x})) θ := by
    simpa [hs] using
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ t x θ).continuousAt
  have hc_0 : ContinuousAt (fun θ' => (M θ').real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x})) θ := by
    simpa [hs] using
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ 0 x θ).continuousAt
  filter_upwards [hc_t.eventually_ne h4', hc_0.eventually_ne h₅] with θ' ht h0
  exact V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ' t x h₀ ht h0


-- created on 2026-10-06
-- updated on 2026-10-20
