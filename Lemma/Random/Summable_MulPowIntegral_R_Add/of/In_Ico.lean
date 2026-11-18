import Lemma.Random.AbsExpect.le.Abs
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` the discounted series `∑ k, γ ^ k * 𝔼[r[t+k] | B]` of the
continuous-action trajectory model is summable.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ)
  (B : Set (ℕ → ℝ × 𝒮 × 𝒜))
  (t : ℕ) :
-- imply
  Summable (fun k => γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B]) := by
-- proof
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|) ?_
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
  apply mul_le_mul_of_nonneg_left
    (AbsExpect.le.Abs h₁ (M := M) (B := B) hR (t + k)) (pow_nonneg h₀.1 k)


-- created on 2026-10-07
-- updated on 2026-11-18