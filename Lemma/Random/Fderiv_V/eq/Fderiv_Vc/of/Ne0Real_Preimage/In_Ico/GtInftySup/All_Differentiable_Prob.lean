import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Syntax.Order.Sup
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Filter


/--
On a reachable state, the derivative of the state value equals that of its time-free closed form:
`fderiv ℝ (fun θ' ↦ V θ' γ t x) θ = fderiv ℝ (fun θ' ↦ V0 θ' γ x) θ`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {x : 𝒮}
  {θ : Θ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (hg : ∀ x, Integrable (g x) μ.measure)
  (hCg : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t x) θ = fderiv ℝ (fun θ' => M.V0 θ' γ x) θ :=
-- proof
  EventuallyEq.fderiv_eq
    (V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
      (M := M) h₀ h₁ hπ h₂ h₃ hg hCg h₄)


-- created on 2026-10-06
-- updated on 2026-11-14
