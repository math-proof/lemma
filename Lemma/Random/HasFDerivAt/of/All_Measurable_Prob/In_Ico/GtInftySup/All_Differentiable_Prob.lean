import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Analysis.Calculus.SmoothSeries
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Random.Summable_MulPowWk.of.In_Ico
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
open MeasureTheory PolicyGradient Random Set


/--
Derivative of the closed-form state value on a general state space: `θ ↦ Vk θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ Wk θ k x) θ`.
Continuous-state counterpart of `Tensor.HasFDerivAt.of.In_Ico.GtInftySup.All_Differentiable_Prob`
(`h₃`: the policy is measurable in the state; `Θ` is finite-dimensional, like the weights `π` of shape `(D,)`).
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
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => M.Vk θ γ x) (∑' k, γ ^ k • fderiv ℝ (fun θ => M.Wk θ k x) θ) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hW := fun k => Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob (M := M) h₃ h₀ hC k x
  apply hasFDerivAt_tsum (Summable_MulPowMulAdd_1.of.In_Ico h₂ (Fintype.card A * Cp * |M.env.R|))
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
      apply mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₂.1 k))
    (Summable_MulPowWk.of.In_Ico (M := M) h₂ θ x) θ


-- created on 2026-10-07
