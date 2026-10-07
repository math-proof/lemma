import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_Qkd.of.All_Measurable_Prob
import Lemma.Real.HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
gradient of the Bellman equation for the closed-form value function with continuous states and a density policy:
`fderiv Vkd(x) = ∫ u, Qkd(x, u) • fderiv π(u | x) du + γ • ∫ u, π(u | x) • ∫ y, fderiv Vkd(y) ∂T(· | x, u) du`.
Continuous-action counterpart of `Random.Fderiv.eq.AddSum_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob`:
both action sums become integrals against the reference measure of `A` (differentiated under the integral sign).
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
  fderiv ℝ (fun θ => M.Vkd θ γ x) θ =
    ∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ ∂ReferenceMeasure.measure +
      γ • ∫ u, M.pol.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.trans_markov
  obtain ⟨Cg, hCg⟩ := id h₃
  have hg : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ g x u := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using h₁ θ x u
  obtain ⟨C, hCV⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  have hQ := fun u θ => DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅ x u θ
  have hQb : ∀ θ u, ‖M.Qkd θ γ x u‖ ≤ |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) := fun θ u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
      (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ y)
    unfold DensityModel.Qkd
    refine (norm_add_le _ _).trans (add_le_add (NormRkd.le.Abs_R (M := M) x u) ?_)
    rw [norm_mul, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₄.1
  have hQ' : ∀ θ u, ‖fderiv ℝ (fun θ => M.Qkd θ γ x u) θ‖ ≤ γ * C := fun θ u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (C := C)
      (f := fun y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ) (Filter.Eventually.of_forall fun y => by
        have h := hCV ⟨(θ, y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
    rw [(hQ u θ).2, norm_smul, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₄.1
  have hD := HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
    (ν := ReferenceMeasure.measure) (f := fun θ u => M.pol.prob θ x u) (G := fun θ u => M.Qkd θ γ x u) (g := g x)
    (B₀ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)) (B₁ := γ * C)
    (fun θ => (h₅ θ).comp measurable_prodMk_left) (h₀ x) (fun θ u => M.pol.nonneg θ x u)
    (fun θ => M.pol.integral_eq_one θ x) (fun θ u => hC θ x u) (h₂ x)
    (fun θ => (Measurable_Qkd.of.All_Measurable_Prob (M := M) h₅ θ γ).comp measurable_prodMk_left)
    (fun u θ => (hQ u θ).1) hQb hQ' θ
  have hb : (fun θ => M.Vkd θ γ x) = fun θ => ∫ u, M.pol.prob θ x u * M.Qkd θ γ x u ∂ReferenceMeasure.measure :=
    funext fun θ => Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) h₅ h₄ θ x
  have hV : HasFDerivAt (fun θ => M.Vkd θ γ x)
      (∫ u, M.pol.prob θ x u • fderiv ℝ (fun θ => M.Qkd θ γ x u) θ ∂ReferenceMeasure.measure +
        ∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ ∂ReferenceMeasure.measure) θ := by
    rw [hb]
    exact hD.1
  have hπQ : ∫ u, M.pol.prob θ x u • fderiv ℝ (fun θ => M.Qkd θ γ x u) θ ∂ReferenceMeasure.measure =
      γ • ∫ u, M.pol.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
    rw [← integral_smul]
    congr 1
    funext u
    rw [(hQ u θ).2, smul_comm]
  rw [hV.fderiv, hπQ, add_comm]


-- created on 2026-10-07
