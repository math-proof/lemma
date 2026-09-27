import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Rewards of the trajectory model are bounded by `R`, hence so is every conditional expected reward:
`‖𝔼[r[t] | B]‖ ≤ ‖R‖` (the conditional measure is `0` on null events).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
-- given
  (B : Set (ℕ → Step S A))
  (t : ℕ) :
-- imply
  ‖∫ ω, r t ω ∂(M.traj θ)[|B]‖ ≤ ‖M.env.R‖ := by
-- proof
  classical
  simpa [Real.norm_eq_abs] using cond_r_bdd M θ B t


-- created on 2026-09-26
