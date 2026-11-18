import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Almost surely every reward of the continuous-action trajectory model is bounded by the reward bound:
`∀ k, ‖r[k]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, ‖r k ω‖ ≤ |R| := by
-- proof
  rw [ae_all_iff]
  exact fun k => (MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) hR θ k).mono fun ω h => by
    rw [h]; exact NormClip.le.Abs_R R _


-- created on 2026-10-20
-- updated on 2026-11-18
