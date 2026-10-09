import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Norm_Integral_R.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Rewards of the trajectory model are bounded by `R`, hence so is every conditional expected reward:
`‖𝔼[r[t] | B]‖ ≤ ‖R‖` (the conditional measure is `0` on null events).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  ‖∫ ω, r t ω ∂(M θ)[|B]‖ ≤ ‖M.env.R‖ := by
-- proof
  classical
  simpa [Real.norm_eq_abs] using Norm_Integral_R.le.Abs_R h₁ (M := M) θ B t


-- created on 2026-09-26
