import Lemma.Random.Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.V.eq.V0.of.Ne0Real_Preimage.In_Ico
import Syntax.Order.Sup
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`ℙ(s[t] = x) ≠ 0` at `θ`), near `θ`:
`M.V θ' γ t x = M.V0 R θ' γ x`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {sₜ : 𝒮}
  {θ : Θ}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π θ z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₃ : sup[sₜ] (∫ u, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ u‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) μ.measure)
  (h₄ : (M θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  (fun θ' => M.V θ' γ t sₜ) =ᶠ[𝓝 θ] fun θ' => M.V0 R θ' γ sₜ := by
-- proof
  obtain ⟨Cg, hCgbound⟩ := id h₃
  have h₅le : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖) ∂μ.measure ≤ Cg := fun x => hCgbound ⟨x, rfl⟩
  have hs : s = fun t ω => (ω t).2.1 :=
    funext₂ fun t ω => (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {sₜ})) θ :=
    (Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₁ hπ h₂ h₅le hBdd hIntg t sₜ θ).continuousAt
  filter_upwards [hc.eventually_ne h₄] with θ' ht
  have ht' : (M θ').real ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω t).2.1) ⁻¹' {sₜ}) ≠ 0 := by
    simpa [hs] using ht
  exact V.eq.V0.of.Ne0Real_Preimage.In_Ico (M := M) h₀ ht' hR


-- created on 2026-10-06
-- updated on 2026-11-18