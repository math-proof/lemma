import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B)
  (h₂ : ∀ x, f x > g x) :
-- imply
  lim [x → x₀] f x ≥ lim [x → x₀] g x := by
-- proof
  rw [h₀.limUnder_eq, h₁.limUnder_eq]
  exact le_of_tendsto_of_tendsto' h₁ h₀ fun x => (h₂ x).le


-- created on 2021-08-29
-- updated on 2023-04-17
