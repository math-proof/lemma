import sympy.sets.sets
import sympy.Basic
import Lemma.Nat.Lt.Lt.is.Lt.Min


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : x < min a b) :
-- imply
  x < a ∧ x < b := by
-- proof
  exact Nat.Lt.Lt.is.Lt.Min.mpr h


-- created on 2026-10-03
