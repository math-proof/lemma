import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Macro.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (a b : ℝ) :
-- imply
  min a b = Minima ({a, b} : Set ℝ) id := by
-- proof
  simp [Minima]


-- created on 2023-04-23
-- updated on 2026-10-26
