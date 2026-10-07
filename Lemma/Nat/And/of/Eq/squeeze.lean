import sympy.Basic
import Lemma.Nat.Eq.of.And.squeeze


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  x ≤ y ∧ x ≥ y := by
-- proof
  exact Nat.Eq.of.And.squeeze h


-- created on 2026-10-03
