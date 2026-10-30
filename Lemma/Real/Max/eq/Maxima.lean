import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Syntax.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (a b : ℝ) :
-- imply
  max a b = Maxima ({a, b} : Set ℝ) id := by
-- proof
  simp [Maxima]


-- created on 2023-04-23
-- updated on 2026-10-26
