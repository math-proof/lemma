import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[path]
private lemma main
  [Nonempty α]
  {S : Set α}
  {f : α → ℝ}
  {x₀ : α}
-- given
  (h₀ : x₀ = ArgMin S f)
  (h₁ : ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y) :
-- imply
  ∀ x ∈ S, f x₀ ≤ f x := by
-- proof
  have hs : ArgMin S f ∈ S ∧ ∀ y ∈ S, f (ArgMin S f) ≤ f y := Classical.epsilon_spec h₁
  rw [← h₀] at hs
  exact hs.2


-- created on 2019-04-14
