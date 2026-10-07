import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
With continuous states and a density policy, `θ ↦ Qkd θ γ x u` is differentiable with derivative
`γ • ∫ y, fderiv ℝ (fun θ ↦ Vkd θ γ y) θ ∂T(· | x, u)` (differentiation under the integral sign).
Continuous-action counterpart of `Random.DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob`.
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
  (u : A)
  (θ : Θ) :
-- imply
  DifferentiableAt ℝ (fun θ => M.Qkd θ γ x u) θ ∧
    fderiv ℝ (fun θ => M.Qkd θ γ x u) θ = γ • ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)) := by
-- proof
  have := M.env.trans_markov
  obtain ⟨C, hC⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  have hV := HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  have hI : HasFDerivAt (fun θ => ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u)))
      (∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ y => M.Vkd θ γ y)
      (F' := fun θ y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ) (s := Set.univ) (bound := fun _ => C) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' => (Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ).aestronglyMeasurable)
      (Integrable.of_bound (Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ γ).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|) (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ y))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ)
        (fun y => (hV y θ).differentiableAt)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y θ' _ => by
        have h := hC ⟨(θ', y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
      (integrable_const _)
      (Filter.Eventually.of_forall fun y θ' _ => (hV y θ').differentiableAt.hasFDerivAt)
  refine ⟨(hI.differentiableAt.const_mul γ).const_add _, ?_⟩
  unfold DensityModel.Qkd
  rw [fderiv_const_add, fderiv_const_mul hI.differentiableAt, hI.fderiv]


-- created on 2026-10-07
