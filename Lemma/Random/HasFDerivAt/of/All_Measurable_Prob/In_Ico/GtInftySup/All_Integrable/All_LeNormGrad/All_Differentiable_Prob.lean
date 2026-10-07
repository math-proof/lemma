import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Analysis.Calculus.SmoothSeries
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Random.Summable_MulPowWkd.of.In_Ico
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
open MeasureTheory PolicyGradient Random Set


/--
Derivative of the closed-form state value with continuous states and a density policy: `θ ↦ Vkd θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ Wkd θ k x) θ`.
Continuous-action counterpart of `Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob`.
`h₀`, `h₁`: `θ ↦ π_θ(u | x)` is differentiable and its gradient is dominated by `g x u`; `h₂`, `h₃`: `g x` is integrable
over the actions, uniformly in the state (this replaces `|A| * sup ‖∇π‖ < ∞` of the finite-action version);
`h₅`: `(x, u) ↦ π_θ(u | x)` is jointly measurable.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
  {g : S → A → ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : ∀ θ x u, ‖∇[θ] M.pol.prob θ x u‖ ≤ g x u)
  (h₂ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₃ : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (x : S)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => M.Vkd θ γ x) (∑' k, γ ^ k • fderiv ℝ (fun θ => M.Wkd θ k x) θ) θ := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₃
  have hg : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ g x u := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using h₁ θ x u
  have hW := fun k => Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob (M := M) h₅ h₀ hC h₂ hg k x
  apply hasFDerivAt_tsum (Summable_MulPowMulAdd_1.of.In_Ico h₄ (Cg * |M.env.R|))
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
      apply mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₄.1 k))
    (Summable_MulPowWkd.of.In_Ico (M := M) h₄ θ x) θ


-- created on 2026-10-07
