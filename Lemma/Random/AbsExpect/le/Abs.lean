import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Rewards of the continuous-action trajectory model are bounded by `R`, hence so is every
conditional expected reward: `‖𝔼[r[t] | B]‖ ≤ |R|` (the conditional measure is `0` on null events).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (B : Set (ℕ → ℝ × 𝒮 × 𝒜))
  (t : ℕ) :
-- imply
  ‖∫ ω, r t ω ∂(M.traj θ)[|B]‖ ≤ |M.R| := by
-- proof
  have hae : ∀ᵐ ω ∂(M.traj θ)[|B], ‖r t ω‖ ≤ |M.R| :=
    cond_absolutelyContinuous.ae_le
      ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ t).mono fun ω h => by
        rw [h]
        exact NormClip.le.Abs_R M.R _)
  if hB : M.traj θ B = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simp
  else
    have := cond_isProbabilityMeasure (μ := M.traj θ) hB
    simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-09-26
-- updated on 2026-11-17