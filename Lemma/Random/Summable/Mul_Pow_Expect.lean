import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
The discounted conditional reward series of the continuous-action trajectory model is summable for `γ ∈ [0, 1)`:
`Summable (k ↦ γ ^ k * 𝔼[r[t + k] | B])`, so the sum is genuine.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (B : Set (ℕ → ℝ × 𝒮 × 𝒜))
  (t : ℕ) :
-- imply
  Summable (fun k => γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B]) := by
-- proof
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg h₀.1 k)
  if hB : (M θ) B = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simp
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have hae : ∀ᵐ ω ∂(M θ)[|B], ‖r (t + k) ω‖ ≤ |M.env.R| :=
      cond_absolutelyContinuous.ae_le
        ((MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (t + k)).mono fun ω h => by
          rw [h]
          apply NormClip.le.Abs_R)
    have h := norm_integral_le_of_norm_le_const hae
    simpa using h


-- created on 2026-09-26
-- updated on 2026-11-14
