import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.AeR.eq.Rc
import Lemma.Random.NormRc.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Conditional expected rewards are bounded: `‖𝔼[r[t] | B]‖ ≤ |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  ‖∫ ω, r t ω ∂(M θ)[|B]‖ ≤ |M.env.R| := by
-- proof
  have hae : ∀ᵐ ω ∂(M θ)[|B], ‖r t ω‖ ≤ |M.env.R| :=
    cond_absolutelyContinuous.ae_le ((AeR.eq.Rc (M := M) θ t).mono fun ω h => by rw [h]; exact NormRc.le.Abs_R (M := M) _)
  if hB : M θ B = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simp
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have h := norm_integral_le_of_norm_le_const hae
    simpa using h


-- created on 2026-10-07
