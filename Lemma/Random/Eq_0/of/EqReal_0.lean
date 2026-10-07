import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
An event of real probability `0` is null: `(M θ).real B = 0 → M θ B = 0`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {B : Set (ℕ → ℝ × S × A)}
-- given
  (θ : Θ)
  (h : (M θ).real B = 0) :
-- imply
  M θ B = 0 := by
-- proof
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h


-- created on 2026-10-07
