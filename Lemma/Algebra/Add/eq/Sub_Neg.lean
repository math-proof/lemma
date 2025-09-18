import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.EqNegNeg
open Algebra


@[main, comm]
private lemma main
  [AddGroup α]
  (a b : α) :
-- imply
  a + b = a - -b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [EqNegNeg]


-- created on 2025-03-16
