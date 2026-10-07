import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import sympy.Basic
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory Real


/--
Differentiation under the integral sign against a parametric probability density:
if `f θ` is a probability density (w.r.t. `ν`) for every `θ`, differentiable in `θ` with `‖fderiv f(·, u)‖ ≤ g u` for an
integrable `g`, and `G` is bounded by `B₀`, differentiable in `θ` with `‖fderiv G(·, u)‖ ≤ B₁` (all measurable in `u`), then
`θ ↦ ∫ u, f θ u * G θ u dν` has derivative `∫ u, f θ u • fderiv G(·, u) θ dν + ∫ u, G θ u • fderiv f(·, u) θ dν`,
whose norm is at most `B₁ + B₀ * ∫ g`.
The dominating function near `θ` is `(f θ + g) * B₁ + B₀ * g` (mean value inequality for `f`), so no uniform bound on
the densities `f θ` is needed.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ] [MeasurableSpace A]
  {ν : Measure A}
  {f G : Θ → A → ℝ}
  {g : A → ℝ}
  {B₀ B₁ : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (f θ))
  (h₁ : ∀ u, Differentiable ℝ (fun θ => f θ u))
  (h₂ : ∀ θ u, f θ u ≥ 0)
  (h₃ : ∀ θ, ∫ u, f θ u ∂ν = 1)
  (h₄ : ∀ θ u, ‖fderiv ℝ (fun θ => f θ u) θ‖ ≤ g u)
  (h₅ : Integrable g ν)
  (h₆ : ∀ θ, Measurable (G θ))
  (h₇ : ∀ u, Differentiable ℝ (fun θ => G θ u))
  (h₈ : ∀ θ u, ‖G θ u‖ ≤ B₀)
  (h₉ : ∀ θ u, ‖fderiv ℝ (fun θ => G θ u) θ‖ ≤ B₁)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => ∫ u, f θ u * G θ u ∂ν)
      (∫ u, f θ u • fderiv ℝ (fun θ => G θ u) θ ∂ν + ∫ u, G θ u • fderiv ℝ (fun θ => f θ u) θ ∂ν) θ ∧
    ‖∫ u, f θ u • fderiv ℝ (fun θ => G θ u) θ ∂ν + ∫ u, G θ u • fderiv ℝ (fun θ => f θ u) θ ∂ν‖ ≤
      B₁ + B₀ * ∫ u, g u ∂ν := by
-- proof
  have hfi : ∀ θ, Integrable (f θ) ν := fun θ =>
    Integrable.of_integral_ne_zero (by rw [h₃ θ]; exact one_ne_zero)
  have hSf : ∀ θ, StronglyMeasurable (fun u => fderiv ℝ (fun θ => f θ u) θ) := fun θ =>
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable h₀ (fun u => (h₁ u) θ)
  have hSG : ∀ θ, StronglyMeasurable (fun u => fderiv ℝ (fun θ => G θ u) θ) := fun θ =>
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable h₆ (fun u => (h₇ u) θ)
  have hb₁ : ∀ θ u, ‖f θ u • fderiv ℝ (fun θ => G θ u) θ‖ ≤ f θ u * B₁ := fun θ u => by
    rw [norm_smul, Real.norm_of_nonneg (h₂ θ u)]
    exact mul_le_mul_of_nonneg_left (h₉ θ u) (h₂ θ u)
  have hb₂ : ∀ θ u, ‖G θ u • fderiv ℝ (fun θ => f θ u) θ‖ ≤ B₀ * g u := fun θ u => by
    rw [norm_smul]
    exact mul_le_mul (h₈ θ u) (h₄ θ u) (norm_nonneg _) ((norm_nonneg _).trans (h₈ θ u))
  have hi₁ : ∀ θ, Integrable (fun u => f θ u • fderiv ℝ (fun θ => G θ u) θ) ν := fun θ =>
    ((hfi θ).mul_const B₁).mono' ((h₀ θ).stronglyMeasurable.smul (hSG θ)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb₁ θ))
  have hi₂ : ∀ θ, Integrable (fun u => G θ u • fderiv ℝ (fun θ => f θ u) θ) ν := fun θ =>
    (h₅.const_mul B₀).mono' ((h₆ θ).stronglyMeasurable.smul (hSf θ)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb₂ θ))
  have hmv : ∀ u, ∀ θ' ∈ Metric.ball θ 1, f θ' u ≤ f θ u + g u := fun u θ' hθ' => by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun θ => f θ u) (C := g u) (s := Set.univ)
      (fun θ _ => (h₁ u) θ) (fun θ _ => h₄ θ u) convex_univ (Set.mem_univ θ) (Set.mem_univ θ')
    have hg : 0 ≤ g u := (norm_nonneg _).trans (h₄ θ u)
    have hd : ‖θ' - θ‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hθ'
    have h₁₀ : f θ' u - f θ u ≤ g u * ‖θ' - θ‖ := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
    have h₁₁ : g u * ‖θ' - θ‖ ≤ g u := mul_le_of_le_one_right hg hd.le
    linarith
  have hm := ((h₀ θ).stronglyMeasurable.smul (hSG θ)).add ((h₆ θ).stronglyMeasurable.smul (hSf θ))
  have hI : HasFDerivAt (fun θ => ∫ u, f θ u * G θ u ∂ν)
      (∫ u, (f θ u • fderiv ℝ (fun θ => G θ u) θ + G θ u • fderiv ℝ (fun θ => f θ u) θ) ∂ν) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ u => f θ u * G θ u)
      (F' := fun θ u => f θ u • fderiv ℝ (fun θ => G θ u) θ + G θ u • fderiv ℝ (fun θ => f θ u) θ)
      (s := Metric.ball θ 1) (bound := fun u => (f θ u + g u) * B₁ + B₀ * g u) (Metric.ball_mem_nhds θ one_pos)
      (Filter.Eventually.of_forall fun θ' => ((h₀ θ').mul (h₆ θ')).aestronglyMeasurable)
      (((hfi θ).mul_const B₀).mono' ((h₀ θ).mul (h₆ θ)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_of_nonneg (h₂ θ u)]
        exact mul_le_mul_of_nonneg_left (h₈ θ u) (h₂ θ u)))
      hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u θ' hθ' => (norm_add_le _ _).trans (add_le_add
        ((hb₁ θ' u).trans (mul_le_mul_of_nonneg_right (hmv u θ' hθ') ((norm_nonneg _).trans (h₉ θ u)))) (hb₂ θ' u)))
      ((((hfi θ).add h₅).mul_const B₁).add (h₅.const_mul B₀))
      (Filter.Eventually.of_forall fun u θ' _ => ((h₁ u) θ').hasFDerivAt.mul ((h₇ u) θ').hasFDerivAt)
  rw [integral_add (hi₁ θ) (hi₂ θ)] at hI
  have e₁ := norm_integral_le_of_norm_le ((hfi θ).mul_const B₁) (Filter.Eventually.of_forall (hb₁ θ))
  have e₂ := norm_integral_le_of_norm_le (h₅.const_mul B₀) (Filter.Eventually.of_forall (hb₂ θ))
  rw [integral_mul_const, h₃, one_mul] at e₁
  rw [integral_const_mul] at e₂
  exact ⟨hI, (norm_add_le _ _).trans (add_le_add e₁ e₂)⟩


-- created on 2026-10-07
