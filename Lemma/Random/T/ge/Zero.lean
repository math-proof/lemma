import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Transition probabilities are nonnegative: `0 ≤ T(x, u, y)`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (x : S)
  (u : A)
  (y : S) :
-- imply
  0 ≤ M.T x u y := by
-- proof
  unfold Model.T; exact measureReal_nonneg


-- created on 2026-10-07
