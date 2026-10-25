import sympy.Basic
import Macro.Order.ExprWithLimits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[path]
private lemma main
  [Nonempty α]
  {S : Set α}
  {f : α → ℝ}
  {x₀ : α}
-- given
  (h₀ : x₀ = min⁻¹[x ∈ S] f x)
  (h₁ : ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y) :
-- imply
  ∀ x ∈ S, f x₀ ≤ f x := by
-- proof
  subst h₀
  exact (Classical.epsilon_spec h₁).2


-- created on 2019-04-14
