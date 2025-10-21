import Lemma.Rat.EqMulDiv.of.Ne_0
import Lemma.Nat.Mul
open Nat Rat


@[main]
private lemma main
  [CommGroupWithZero α]
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a * (b / a) = b := by
-- proof
  rw [Mul.comm]
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-04-02
