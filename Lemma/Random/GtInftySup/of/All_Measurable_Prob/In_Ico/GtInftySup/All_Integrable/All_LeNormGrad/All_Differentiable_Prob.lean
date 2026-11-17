import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Mathlib.Analysis.Calculus.SmoothSeries
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient Random Set


/--
For a differentiable density policy with an integrably dominated gradient, the closed-form state value with continuous
states and actions has a bounded gradient: `sup[θ, y] ‖∇[θ] V0 θ γ y‖ < ∞`.
`h₀`, `h₁`: `θ ↦ π_θ(u | x)` is differentiable and its gradient is dominated by `g x u`; `h₂`, `h₃`: `g x` is integrable
over the actions, uniformly in the state (this replaces `|𝒜| * sup ‖∇π‖ < ∞` of the finite-action version);
`h₅`: `(x, u) ↦ π_θ(u | x)` is jointly measurable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h₀ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₁ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  :
-- imply
  sup[θ, y] ‖∇[θ] M.V0 θ γ y‖ < ∞ := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₁
  have hg : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure ≤ Cg := by
    intro x
    exact hCg ⟨x, rfl⟩
  refine ⟨∑' k : ℕ, γ ^ k * ((k + 1) * (Cg * |M.R|)), ?_⟩
  rintro _ ⟨⟨θ, y⟩, rfl⟩
  show ‖gradient (fun θ => M.V0 θ γ y) θ‖ ≤ _
  rw [gradient, LinearIsometryEquiv.norm_map,
    (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ hBdd hIntg h₄ h₅ y θ).fderiv]
  have hsum : Summable (fun k : ℕ => γ ^ k * ((k + 1) * (Cg * |M.R|))) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * γ ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg h₄.1]; exact h₄.2)
    have h2 := summable_geometric_of_lt_one h₄.1 h₄.2
    exact ((h1.add h2).mul_right (Cg * |M.R|)).congr fun k => by ring
  refine tsum_of_norm_bounded hsum.hasSum fun k => ?_
  rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
  apply mul_le_mul_of_nonneg_left
    ((Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob (M := M) h₅ h₀ hg hBdd hIntg k y).2 θ)
    (pow_nonneg h₄.1 k)


-- created on 2026-10-07
-- updated on 2026-11-17