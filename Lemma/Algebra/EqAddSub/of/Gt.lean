import sympy.functions.elementary.integers
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b > a) :
-- imply
  b - a + a = b := by
-- proof
  apply EqAddSub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-18
