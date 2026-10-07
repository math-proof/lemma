import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral_R.eq.Sum_MulRealWRc
import Lemma.Random.Sum_Real.eq.One
import Lemma.Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
For a differentiable policy with derivative bounded by `Cp`, `θ ↦ 𝔼[r[t]]` is differentiable with derivative
bounded by `(t + 1) * (|A| * Cp * |R|)`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {Cp : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp)
  (t : ℕ) :
-- imply
  Differentiable ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ‖ ≤
    (t + 1) * (Fintype.card A * Cp * |M.env.R|) := by
-- proof
  have e : (fun θ => ∫ ω, r t ω ∂(M θ)) = fun θ => ∑ x, M.env.init.real {x} * M.W θ M.rc t x :=
    funext fun θ => Random.Integral_R.eq.Sum_MulRealWRc (M := M) θ t
  rw [e]
  have hW := fun x => Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob (M := M) h₀ h₁ (rc_sm M) (rc_bdd M) t x
  refine ⟨fun θ => DifferentiableAt.fun_sum fun x _ => ((hW x).1 θ).const_mul _, fun θ => ?_⟩
  rw [fderiv_fun_sum fun x _ => ((hW x).1 θ).const_mul _]
  calc _ ≤ ∑ x, ‖fderiv ℝ (fun θ => M.env.init.real {x} * M.W θ M.rc t x) θ‖ := norm_sum_le _ _
    _ ≤ ∑ x, M.env.init.real {x} * ((t + 1) * (Fintype.card A * Cp * |M.env.R|)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [fderiv_const_mul ((hW x).1 θ), norm_smul, Real.norm_of_nonneg measureReal_nonneg]
        exact mul_le_mul_of_nonneg_left ((hW x).2 θ) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, Random.Sum_Real.eq.One, one_mul]


-- created on 2026-10-06
