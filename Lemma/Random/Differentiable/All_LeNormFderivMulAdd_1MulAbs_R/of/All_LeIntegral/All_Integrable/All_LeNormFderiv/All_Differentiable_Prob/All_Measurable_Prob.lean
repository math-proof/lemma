import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.MeasurableRkd
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Lemma.Real.HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
If every `θ ↦ π_θ(u | x)` is differentiable with `‖fderiv π(u | x)‖ ≤ g x u`, where `g x` is integrable over the actions
with `∫ g x ≤ Cg` (and `π` is jointly measurable in `(x, u)`), then `θ ↦ Wkd θ k x` is differentiable with derivative
bounded by `(k + 1) * (Cg * |R|)`.
Continuous-action counterpart of
`Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob`:
the finite action sum becomes an integral against the reference measure of `A`, and `|A| * Cp` becomes `Cg`; both the
action and the next-state integrals are differentiated under the integral sign.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {g : S → A → ℝ}
  {Cg : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₄ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (k : ℕ)
  (x : S) :
-- imply
  Differentiable ℝ (fun θ => M.Wkd θ k x) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => M.Wkd θ k x) θ‖ ≤ (k + 1) * (Cg * |M.env.R|) := by
-- proof
  have hR : ∀ x, |M.env.R| * ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg * |M.env.R| := fun x => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (h₄ x) (abs_nonneg _)
  induction k generalizing x with
  | zero =>
    have hD := fun θ => HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
      (ν := ReferenceMeasure.measure) (f := fun θ u => M.pol.prob θ x u) (G := fun _ u => M.rkd x u) (g := g x)
      (B₀ := |M.env.R|) (B₁ := 0)
      (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ x) (fun θ u => M.pol.nonneg θ x u)
      (fun θ => M.pol.integral_eq_one θ x) (fun θ u => h₂ θ x u) (h₃ x)
      (fun _ => (MeasurableRkd (M := M)).comp measurable_prodMk_left) (fun u => differentiable_const _)
      (fun _ u => NormRkd.le.Abs_R (M := M) x u) (fun θ u => by simp) θ
    have hW : ∀ θ, HasFDerivAt (fun θ => M.Wkd θ 0 x) _ θ := fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv, Nat.cast_zero, zero_add, one_mul]
    linarith [(hD θ).2, hR x]
  | succ k ih =>
    have := M.env.trans_markov
    have hT : ∀ θ, Measurable (fun u => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) := fun θ =>
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.Wkd θ k z.2)
        ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable).comp measurable_prodMk_left
    have hI : ∀ u θ, HasFDerivAt (fun θ => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)))
        (∫ y, fderiv ℝ (fun θ => M.Wkd θ k y) θ ∂(M.env.trans (x, u))) θ := fun u θ =>
      hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ y => M.Wkd θ k y)
        (F' := fun θ y => fderiv ℝ (fun θ => M.Wkd θ k y) θ) (s := Set.univ)
        (bound := fun _ => ((k : ℝ) + 1) * (Cg * |M.env.R|)) Filter.univ_mem
        (Filter.Eventually.of_forall fun θ' => (Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ' k).aestronglyMeasurable)
        (Integrable.of_bound (Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).aestronglyMeasurable |M.env.R|
          (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ k y))
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' => Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ' k) (fun y => (ih y).1 θ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y θ' _ => (ih y).2 θ')
        (integrable_const _)
        (Filter.Eventually.of_forall fun y θ' _ => ((ih y).1 θ').hasFDerivAt)
    have hg' : ∀ θ u, ‖fderiv ℝ (fun θ => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) θ‖ ≤
        ((k : ℝ) + 1) * (Cg * |M.env.R|) := fun θ u => by
      rw [(hI u θ).fderiv]
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall fun y => (ih y).2 θ)
      simpa using h
    have hgb : ∀ θ u, ‖∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))‖ ≤ |M.env.R| := fun θ u => by
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ k y)
      simpa using h
    have hD := fun θ => HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
      (ν := ReferenceMeasure.measure) (f := fun θ u => M.pol.prob θ x u)
      (G := fun θ u => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) (g := g x)
      (B₀ := |M.env.R|) (B₁ := ((k : ℝ) + 1) * (Cg * |M.env.R|))
      (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ x) (fun θ u => M.pol.nonneg θ x u)
      (fun θ => M.pol.integral_eq_one θ x) (fun θ u => h₂ θ x u) (h₃ x)
      hT (fun u θ => (hI u θ).differentiableAt) hgb hg' θ
    have hW : ∀ θ, HasFDerivAt (fun θ => M.Wkd θ (k + 1) x) _ θ := fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv]
    push_cast
    linarith [(hD θ).2, hR x]


-- created on 2026-10-07
