import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Syntax.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {c : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (f '' S))
  (h₂ : Minima S f ≤ c) :
-- imply
  sInf (insert c (f '' S)) = Minima S f := by
-- proof
  rw [csInf_insert h₁ (h₀.image f)]
  apply min_eq_right h₂


-- created on 2023-04-23
-- updated on 2026-10-26
