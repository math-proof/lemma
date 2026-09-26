import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B) :
-- imply
  (lim [x → x₀] (f x + g x)) = (lim [x → x₀] f x) + (lim [x → x₀] g x) := by
-- proof
  rw [h₀.limUnder_eq, h₁.limUnder_eq]
  exact (h₀.add h₁).limUnder_eq


@[main]
private lemma inf
  {f g : ℕ → ℝ}
  {A B : ℝ}
-- given
  (h₀ : lim [n → ∞] f n = A)
  (h₁ : lim [n → ∞] g n = B) :
-- imply
  (lim [n → ∞] (f n + g n)) = (lim [n → ∞] f n) + (lim [n → ∞] g n) := by
-- proof
  rw [h₀.limUnder_eq, h₁.limUnder_eq]
  exact (h₀.add h₁).limUnder_eq


-- created on 2026-09-26
