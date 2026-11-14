import Lemma.Random.Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.V.eq.V0.of.Ne0Real_Preimage.In_Ico
import Syntax.Order.Sup
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
On a reachable state (`ℙ(s[t] = x) ≠ 0` at `θ`), near `θ`:
`M.V θ' γ t x = M.V0 θ' γ x`.
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
  (fun θ' => M.V θ' γ t x) =ᶠ[𝓝 θ] fun θ' => M.V0 θ' γ x := by
-- proof
  obtain ⟨Cg, hCgbound⟩ := id hCg
  have h₅le : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hCgbound ⟨x, rfl⟩
  have hs : s = fun t ω => (ω t).2.1 :=
    funext₂ fun t ω => (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {x})) θ :=
    (Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₁ hπ h₂ h₃ hg h₅le t x θ).continuousAt
  filter_upwards [hc.eventually_ne h₄] with θ' ht
  have ht' : (M θ').real ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω t).2.1) ⁻¹' {x}) ≠ 0 := by
    simpa [hs] using ht
  exact V.eq.V0.of.Ne0Real_Preimage.In_Ico (M := M) h₀ ht'


-- created on 2026-10-06
-- updated on 2026-11-14
