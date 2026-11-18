import Def.Analysis.Calculus.Gradient.Operators.Part2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Real.HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
If every `θ ↦ π_θ(u | x)` is differentiable with `‖fderiv π(u | x)‖ ≤ g x u`, where `g x` is integrable over the actions
with `∫ g x ≤ Cg` (and `π` is jointly measurable in `(x, u)`), then `θ ↦ Wkd θ k x` is differentiable with derivative
bounded by `(k + 1) * (Cg * |R|)`.
Continuous-action counterpart of
`Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob`:
the finite action sum becomes an integral against the reference measure of `𝒜`, and `|𝒜| * Cp` becomes `Cg`; both the
action and the next-state integrals are differentiated under the integral sign.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {Cg : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂μ.measure ≤ Cg)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (R : ℝ)
  (k : ℕ)
  (sₜ : 𝒮) :
-- imply
  Differentiable ℝ (fun θ => M.Wkd R θ k sₜ) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => M.Wkd R θ k sₜ) θ‖ ≤ (k + 1) * (Cg * |R|) := by
-- proof
  let g : 𝒮 → 𝒜 → ℝ :=
    fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)
  have hBound : ∀ θ sₜ aₜ, ‖fderiv ℝ (fun θ => M.π[θ] sₜ aₜ) θ‖ ≤ g sₜ aₜ := by
    intro θ sₜ aₜ
    have : ‖∇[θ] M.π[θ] sₜ aₜ‖ ≤ g sₜ aₜ := by
      refine le_csSup ?_ ⟨θ, rfl⟩
      exact hBdd sₜ aₜ
    simpa [gradient, LinearIsometryEquiv.norm_map] using this
  have hInt : ∀ x, Integrable (g x) μ.measure := by
    intro x
    exact hIntg x
  have hR : ∀ x, |R| * ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg * |R| := fun x => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (h₂ x) (abs_nonneg _)
  induction k generalizing sₜ with
  | zero =>
    have hD := fun θ => HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
      (ν := ReferenceMeasure.measure) (f := fun θ u => M.π[θ] sₜ u) (G := fun _ u => M.rkd R sₜ u) (g := g sₜ)
      (B₀ := |R|) (B₁ := 0)
      (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ sₜ) (fun θ u => hStoch.nonneg θ sₜ u)
      (fun θ => hStoch.integral_eq_one θ sₜ) (fun θ u => hBound θ sₜ u) (hInt sₜ)
      (fun _ => (MeasurableRkd (M := M) R).comp measurable_prodMk_left) (fun u => differentiable_const _)
      (fun _ u => NormRkd.le.Abs_R (M := M) R sₜ u) (fun θ u => by simp) θ
    have hW : ∀ θ, HasFDerivAt (fun θ => M.Wkd R θ 0 sₜ) _ θ := fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv, Nat.cast_zero, zero_add, one_mul]
    linarith [(hD θ).2, hR sₜ]
  | succ k ih =>
    have hT : ∀ θ, Measurable (fun u => ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))) := fun θ =>
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK) (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd R θ k z.2)
        ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ R θ k).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable).comp measurable_prodMk_left
    have hI : ∀ u θ, HasFDerivAt (fun θ => ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u)))
        (∫ y, fderiv ℝ (fun θ => M.Wkd R θ k y) θ ∂(M.trans (sₜ, u))) θ := fun u θ =>
      hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ y => M.Wkd R θ k y)
        (F' := fun θ y => fderiv ℝ (fun θ => M.Wkd R θ k y) θ) (s := Set.univ)
        (bound := fun _ => ((k : ℝ) + 1) * (Cg * |R|)) Filter.univ_mem
        (Filter.Eventually.of_forall fun θ' => (Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ R θ' k).aestronglyMeasurable)
        (Integrable.of_bound (Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ R θ k).aestronglyMeasurable |R|
          (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) R θ k y))
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' => Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ R θ' k) (fun y => (ih y).1 θ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y θ' _ => (ih y).2 θ')
        (integrable_const _)
        (Filter.Eventually.of_forall fun y θ' _ => ((ih y).1 θ').hasFDerivAt)
    have hg' : ∀ θ u, ‖fderiv ℝ (fun θ => ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))) θ‖ ≤
        ((k : ℝ) + 1) * (Cg * |R|) := fun θ u => by
      rw [(hI u θ).fderiv]
      have h := norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u)) (Filter.Eventually.of_forall fun y => (ih y).2 θ)
      simpa using h
    have hgb : ∀ θ u, ‖∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))‖ ≤ |R| := fun θ u => by
      have h := norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u))
        (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) R θ k y)
      simpa using h
    have hD := fun θ => HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
      (ν := ReferenceMeasure.measure) (f := fun θ u => M.π[θ] sₜ u)
      (G := fun θ u => ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))) (g := g sₜ)
      (B₀ := |R|) (B₁ := ((k : ℝ) + 1) * (Cg * |R|))
      (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ sₜ) (fun θ u => hStoch.nonneg θ sₜ u)
      (fun θ => hStoch.integral_eq_one θ sₜ) (fun θ u => hBound θ sₜ u) (hInt sₜ)
      hT (fun u θ => (hI u θ).differentiableAt) hgb hg' θ
    have hW : ∀ θ, HasFDerivAt (fun θ => M.Wkd R θ (k + 1) sₜ) _ θ := fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv]
    push_cast
    linarith [(hD θ).2, hR sₜ]


-- created on 2026-10-07
-- updated on 2026-11-18