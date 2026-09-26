import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {g : ℝ → ℝ}
  {x₀ y : ℝ}
-- given
  (h : lim [x → x₀] g x = y)
  (hy : y ∈ Ioi 0) :
-- imply
  lim [x → x₀] |g x| = lim [x → x₀] g x := by
-- proof
  rw [h.limUnder_eq, ← abs_of_pos (Set.mem_Ioi.mp hy)]
  exact h.abs


-- created on 2026-09-26
