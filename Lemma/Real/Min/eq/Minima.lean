import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  (a b : ℝ) :
-- imply
  min a b = Minima ({a, b} : Set ℝ) id := by
-- proof
  simp [Minima]


-- created on 2026-10-11
-- updated on 2026-10-17
