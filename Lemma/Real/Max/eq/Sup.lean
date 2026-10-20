import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.Basic


@[path]
private lemma main
  (a b : ℝ) :
-- imply
  max a b = sSup {a, b} := by
-- proof
  rw [csSup_pair]


-- created on 2023-04-23
-- updated on 2026-10-17
