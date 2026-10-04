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
  (lim [x → x₀] f x) * y = lim [x → x₀] (f x * y) := by
-- proof
  have h₁ : lim [x → x₀] (f x * y) = A * y := h.mul_const y
  rw [h₁.limUnder_eq, h.limUnder_eq]


-- created on 2020-05-03
