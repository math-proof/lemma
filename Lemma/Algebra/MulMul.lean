import Lemma.Algebra.Mul
import Lemma.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma Comm
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = a * c * b := by
-- proof
  repeat rw [Mul.comm (b := c)]
  rw [Mul_Mul.eq.MulMul]


-- created on 2024-11-29
