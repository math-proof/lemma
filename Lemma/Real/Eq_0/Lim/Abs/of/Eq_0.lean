import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h₀ : lim [x → x₀] g x = 0) :
-- imply
  lim [x → x₀] |g x| = 0 := by
-- proof
  simpa using h₀.abs


-- created on 2023-04-18
