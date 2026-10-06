import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
The initial state distribution of the trajectory model sums to `1`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A} :
-- imply
  ∑ x, M.env.init.real {x} = 1 := by
-- proof
  have := M.env.init_prob
  rw [sum_measureReal_singleton]
  simp


-- created on 2026-10-06
