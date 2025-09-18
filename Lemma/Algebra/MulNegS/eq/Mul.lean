import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.Mul_Neg.eq.NegMul
import Lemma.Algebra.EqNegNeg
open Algebra


@[main]
private lemma main
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a * -b = a * b := by
-- proof
  rw [MulNeg.eq.NegMul]
  rw [Mul_Neg.eq.NegMul]
  rw [EqNegNeg]


-- created on 2025-04-18
