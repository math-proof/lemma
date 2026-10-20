import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
Almost surely every reward of the continuous-action trajectory model is bounded by the reward bound:
`∀ k, ‖r[k]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
-- proof
  rw [ae_all_iff]
  exact fun k => (MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ k).mono fun ω h => by
    rw [h]; exact NormClip.le.Abs_R M.env.R _


-- created on 2026-10-20
