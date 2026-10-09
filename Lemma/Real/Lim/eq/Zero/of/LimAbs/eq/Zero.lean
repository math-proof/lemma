import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h₀ : lim [x → x₀] |g x| = 0) :
-- imply
  lim [x → x₀] g x = 0 := by
-- proof
  rw [Metric.tendsto_nhds] at h₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h₀ ε hε] with _ hx
  simp only [Real.dist_eq, sub_zero, abs_abs] at hx
  rwa [Real.dist_eq, sub_zero]


-- created on 2023-04-18
