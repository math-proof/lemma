import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {x₀ y A : ℝ}
-- given
  (h : lim [x → x₀] f x = A) :
-- imply
  lim [x → x₀] (y * f x) = y * lim [x → x₀] f x := by
-- proof
  rw [h.limUnder_eq]
  exact h.const_mul y


-- created on 2026-09-26
