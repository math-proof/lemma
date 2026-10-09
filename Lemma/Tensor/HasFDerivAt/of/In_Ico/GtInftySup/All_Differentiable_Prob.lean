import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Derivative of the time-free closed-form state value: `θ ↦ Vc θ γ x` has derivative
`∑' k, γ ^ k • fderiv ℝ (fun θ ↦ W θ rc k x) θ`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (x : S)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => M.Vc θ γ x) (∑' k, γ ^ k • fderiv ℝ (fun θ => M.W θ M.rc k x) θ) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hW := fun k => Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob (M := M) h₀ hC (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) k x
  exact hasFDerivAt_tsum (Set.Summable_MulPowMulAdd_1.of.In_Ico h₂ (Fintype.card A * Cp * |M.env.R|))
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
      exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₂.1 k))
    (Summable_MulPowWRc.of.In_Ico (M := M) h₂ θ x) θ


-- created on 2026-10-06
