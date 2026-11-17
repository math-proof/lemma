import Def.Analysis.Calculus.Gradient.Operators.Part2
import Syntax.Order.Sup
import Mathlib.Analysis.Calculus.SmoothSeries
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Random.Summable_MulPowWkd.of.In_Ico
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient Random Set


/--
Derivative of the closed-form state value with continuous states and a density policy: `θ ↦ V0 θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ Wkd θ k x) θ`.
Continuous-action counterpart of `Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob`.
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
  (sₜ : 𝒮)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => M.V0 θ γ sₜ) (∑' k, γ ^ k • fderiv ℝ (fun θ => M.Wkd θ k sₜ) θ) θ := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₁
  have hg : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure ≤ Cg := by
    intro x
    exact hCg ⟨x, rfl⟩
  have hW := fun k => Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob (M := M) h₅ h₀ hg hBdd hIntg k sₜ
  have hEq : (fun θ => M.V0 θ γ sₜ) = fun θ => ∑' k, γ ^ k * M.Wkd θ k sₜ := rfl
  rw [hEq]
  have hsum : Summable (fun k : ℕ => γ ^ k * ((k + 1) * (Cg * |M.R|))) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * γ ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg h₄.1]; exact h₄.2)
    have h2 := summable_geometric_of_lt_one h₄.1 h₄.2
    exact ((h1.add h2).mul_right (Cg * |M.R|)).congr fun k => by ring
  apply hasFDerivAt_tsum hsum
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
      apply mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₄.1 k))
    (Summable_MulPowWkd.of.In_Ico (M := M) h₄ θ sₜ) θ


-- created on 2026-10-07
-- updated on 2026-11-17