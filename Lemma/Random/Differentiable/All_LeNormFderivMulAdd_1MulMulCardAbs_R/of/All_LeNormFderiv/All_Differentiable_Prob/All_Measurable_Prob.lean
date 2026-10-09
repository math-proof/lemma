import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.NormRk.le.Abs_R
import Lemma.Random.NormWk.le.Abs_R
import Lemma.Random.Measurable_Wk.of.All_Measurable_Prob
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
If every `θ ↦ π_θ(u | x)` is differentiable with derivative bounded by `Cp` (and measurable in `x`), then on a general
state space `θ ↦ Wk θ k x` is differentiable with derivative bounded by `(k + 1) * (|A| * Cp * |R|)`.
Continuous-state counterpart of
`Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob`
(for `f = rc`): the finite next-state sum becomes an integral, differentiated under the integral sign
(the derivatives are uniformly bounded and `T(· | x, u)` is a probability measure).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {Cp : ℝ}
-- given
  (h₀ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp)
  (k : ℕ)
  (x : S) :
-- imply
  Differentiable ℝ (fun θ => M.Wk θ k x) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => M.Wk θ k x) θ‖ ≤ (k + 1) * (Fintype.card A * Cp * |M.env.R|) := by
-- proof
  induction k generalizing x with
  | zero =>
    have e : (fun θ => M.Wk θ 0 x) = fun θ => ∑ u, M.pol.prob θ x u * M.rk x u := rfl
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((h₁ x u) θ).mul_const _, fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((h₁ x u) θ).mul_const _]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u * M.rk x u) θ‖ := norm_sum_le _ _
      _ ≤ ∑ _ : A, |M.env.R| * Cp := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_mul_const ((h₁ x u) θ), norm_smul]
          apply mul_le_mul (NormRk.le.Abs_R (M := M) x u) (h₂ θ x u) (norm_nonneg _) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; push_cast; ring
  | succ k ih =>
    have := M.env.trans_markov
    have hI : ∀ u θ, HasFDerivAt (fun θ => ∫ y, M.Wk θ k y ∂(M.env.trans (x, u)))
        (∫ y, fderiv ℝ (fun θ => M.Wk θ k y) θ ∂(M.env.trans (x, u))) θ := fun u θ =>
      hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ y => M.Wk θ k y)
        (F' := fun θ y => fderiv ℝ (fun θ => M.Wk θ k y) θ) (s := Set.univ)
        (bound := fun _ => ((k : ℝ) + 1) * (Fintype.card A * Cp * |M.env.R|)) Filter.univ_mem
        (Filter.Eventually.of_forall fun θ' => (Measurable_Wk.of.All_Measurable_Prob (M := M) h₀ θ' k).aestronglyMeasurable)
        (Integrable.of_bound (Measurable_Wk.of.All_Measurable_Prob (M := M) h₀ θ k).aestronglyMeasurable |M.env.R|
          (Filter.Eventually.of_forall fun y => NormWk.le.Abs_R (M := M) θ k y))
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' => Measurable_Wk.of.All_Measurable_Prob (M := M) h₀ θ' k) (fun y => (ih y).1 θ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y θ' _ => (ih y).2 θ')
        (integrable_const _)
        (Filter.Eventually.of_forall fun y θ' _ => ((ih y).1 θ').hasFDerivAt)
    have hg' : ∀ u θ, ‖fderiv ℝ (fun θ => ∫ y, M.Wk θ k y ∂(M.env.trans (x, u))) θ‖ ≤
        ((k : ℝ) + 1) * (Fintype.card A * Cp * |M.env.R|) := fun u θ => by
      rw [(hI u θ).fderiv]
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall fun y => (ih y).2 θ)
      simpa using h
    have hgb : ∀ u θ, ‖∫ y, M.Wk θ k y ∂(M.env.trans (x, u))‖ ≤ |M.env.R| := fun u θ => by
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (Filter.Eventually.of_forall fun y => NormWk.le.Abs_R (M := M) θ k y)
      simpa using h
    have e : (fun θ => M.Wk θ (k + 1) x) =
        fun θ => ∑ u, M.pol.prob θ x u * ∫ y, M.Wk θ k y ∂(M.env.trans (x, u)) := rfl
    have hg : ∀ u θ, DifferentiableAt ℝ (fun θ => ∫ y, M.Wk θ k y ∂(M.env.trans (x, u))) θ :=
      fun u θ => (hI u θ).differentiableAt
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((h₁ x u) θ).fun_mul (hg u θ), fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((h₁ x u) θ).fun_mul (hg u θ)]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u * ∫ y, M.Wk θ k y ∂(M.env.trans (x, u))) θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ u, (M.pol.prob θ x u * (((k : ℝ) + 1) * (Fintype.card A * Cp * |M.env.R|)) + |M.env.R| * Cp) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_fun_mul ((h₁ x u) θ) (hg u θ)]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          ·
            rw [norm_smul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
            apply mul_le_mul_of_nonneg_left (hg' u θ) (M.pol.nonneg θ x u)
          ·
            rw [norm_smul]
            apply mul_le_mul (hgb u θ) (h₂ θ x u) (norm_nonneg _) (abs_nonneg _)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.pol.sum_eq_one, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          push_cast; ring


-- created on 2026-10-07
