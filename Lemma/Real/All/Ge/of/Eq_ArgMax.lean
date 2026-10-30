import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x₀ : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : ∃ x ∈ S, ∀ y ∈ S, f y ≤ f x)
  (h : x₀ = max⁻¹[x ∈ S] f x) :
-- imply
  ∀ x ∈ S, f x₀ ≥ f x := by
-- proof
  subst h
  exact (Classical.epsilon_spec h₀).2


-- created on 2019-04-13
