import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B)
  (h₂ : f ≥ g) :
-- imply
  lim [x → x₀] f x ≥ lim [x → x₀] g x := by
-- proof
  rw [h₀.limUnder_eq, h₁.limUnder_eq]
  exact le_of_tendsto_of_tendsto' h₁ h₀ h₂


-- created on 2026-09-26
