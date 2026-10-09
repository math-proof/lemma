import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Measurable_Vk.of.All_Measurable_Prob
import Lemma.Random.NormVk.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
On a general state space `θ ↦ Qk θ γ x u` is differentiable with derivative
`γ • ∫ y, fderiv ℝ (fun θ ↦ Vk θ γ y) θ ∂T(· | x, u)` (differentiation under the integral sign).
Continuous-state counterpart of `Tensor.DifferentiableAt.Fderiv.eq.SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (h₃ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (x : S)
  (u : A)
  (θ : Θ) :
-- imply
  DifferentiableAt ℝ (fun θ => M.Qk θ γ x u) θ ∧
    fderiv ℝ (fun θ => M.Qk θ γ x u) θ = γ • ∫ y, fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂(M.env.trans (x, u)) := by
-- proof
  have := M.env.trans_markov
  obtain ⟨C, hC⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃
  have hV := HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃
  have hI : HasFDerivAt (fun θ => ∫ y, M.Vk θ γ y ∂(M.env.trans (x, u)))
      (∫ y, fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂(M.env.trans (x, u))) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ y => M.Vk θ γ y)
      (F' := fun θ y => fderiv ℝ (fun θ => M.Vk θ γ y) θ) (s := Set.univ) (bound := fun _ => C) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' => (Measurable_Vk.of.All_Measurable_Prob (M := M) h₃ θ' γ).aestronglyMeasurable)
      (Integrable.of_bound (Measurable_Vk.of.All_Measurable_Prob (M := M) h₃ θ γ).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|) (Filter.Eventually.of_forall fun y => NormVk.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₂ θ y))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        (fun θ' => Measurable_Vk.of.All_Measurable_Prob (M := M) h₃ θ' γ)
        (fun y => (hV y θ).differentiableAt)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y θ' _ => by
        have h := hC ⟨(θ', y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
      (integrable_const _)
      (Filter.Eventually.of_forall fun y θ' _ => (hV y θ').differentiableAt.hasFDerivAt)
  refine ⟨(hI.differentiableAt.const_mul γ).const_add _, ?_⟩
  unfold Model.Qk
  rw [fderiv_const_add, fderiv_const_mul hI.differentiableAt, hI.fderiv]


-- created on 2026-10-07
