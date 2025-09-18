import Lemma.Algebra.EqMulDiv.of.Ne_0
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  [Field α]
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a * (b / a) = b := by
-- proof
  rw [Mul.comm]
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-04-02
