import Lemma.Algebra.EqMulDiv.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Algebra Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {b : α}
-- given
  (h : b > 0)
  (a : α) :
-- imply
  a / b * b = a := by
-- proof
  have h := Ne.of.Gt h
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-05-04
