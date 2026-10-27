import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Macro.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : ∀ x ∈ S, f x = g x) :
-- imply
  Minima S f = Minima S g := by
-- proof
  rw [Minima, Minima]
  apply congrArg sInf
  apply Set.image_congr h₀


-- created on 2019-04-08
-- updated on 2026-10-26
