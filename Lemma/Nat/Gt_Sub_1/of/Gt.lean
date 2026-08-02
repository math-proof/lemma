import Lemma.Nat.NotLe.of.Gt
import Lemma.Nat.NotLt.is.Ge
import sympy.functions.elementary.integers
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x > y) :
-- imply
  x > y - 1 := by
-- proof
  by_contra h'
  have h' := Le.of.NotGt h'
  have h_le := le_trans h' (IntegerRing.pred_le y)
  exact (NotLe.of.Gt h) h_le


-- created on 2025-08-02
