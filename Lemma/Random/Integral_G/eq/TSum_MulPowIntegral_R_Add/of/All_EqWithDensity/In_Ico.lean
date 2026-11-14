import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
For `γ ∈ [0, 1)` and an arbitrary conditioning set (event) `B` of trajectories, in integral form:
`∫ G[t] d(M θ)[|B] = ∑' k, γ ^ k * ∫ r[t+k] d(M θ)[|B]`.
This is linearity of the elementary conditional measure through the discounted sum
(dominated convergence: the rewards are a.s. bounded by `|R|`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (B : Set (ℕ → ℝ × 𝒮 × 𝒜))
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ)[|B] =
    ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  show ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|B] =
    ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B]
  if hB : (M θ) B = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hB]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have hae : ∀ᵐ ω ∂(M θ)[|B], ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
      apply cond_absolutelyContinuous.ae_le
      exact ae_all_iff.2 fun k =>
        (MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁ θ k).mono fun ω hω => by
          rw [hω]
          exact NormClip.le.Abs_R M.env.R (ω k).1
    have hm : ∀ k, Measurable (r k) := fun k =>
      Random.Measurable.of.All_Eq.fst h₁ k
    have hF : ∀ k, Integrable (fun ω => γ ^ k * r (t + k) ω) (M θ)[|B] := fun k =>
      Integrable.of_bound ((hm (t + k)).const_mul (γ ^ k)).aestronglyMeasurable (γ ^ k * |M.env.R|)
        (hae.mono fun ω hω => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
          exact mul_le_mul_of_nonneg_left (hω (t + k)) (pow_nonneg h₀.1 k))
    have hS : Summable (fun k => ∫ ω, ‖γ ^ k * r (t + k) ω‖ ∂(M θ)[|B]) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      have hb : ∀ᵐ ω ∂(M θ)[|B], ‖‖γ ^ k * r (t + k) ω‖‖ ≤ γ ^ k * |M.env.R| :=
        hae.mono fun ω hω => by
          rw [norm_norm, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
          exact mul_le_mul_of_nonneg_left (hω (t + k)) (pow_nonneg h₀.1 k)
      have := norm_integral_le_of_norm_le_const hb
      simp only [probReal_univ, mul_one] at this
      exact (Real.le_norm_self _).trans this
    rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
    congr 1
    funext k
    exact integral_const_mul _ _


-- created on 2026-11-14
