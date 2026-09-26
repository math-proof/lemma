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
  (h₀ : lim [x → x₀] g x = y)
  (h₁ : y ∈ Iio 0) :
-- imply
  lim [x → x₀] |g x| = -lim [x → x₀] g x := by
-- proof
  rw [h₀.limUnder_eq, ← abs_of_neg (Set.mem_Iio.mp h₁)]
  exact h₀.abs


-- created on 2026-09-26
