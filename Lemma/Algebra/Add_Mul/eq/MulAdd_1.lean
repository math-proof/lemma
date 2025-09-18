import Lemma.Algebra.Add_Mul.eq.MulAdd1
import Lemma.Algebra.Add
open Algebra


@[main, comm]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  d + k * d = (k + 1) * d := by
-- proof
  rw [Add_Mul.eq.MulAdd1]
  rw [Add.comm]


-- created on 2025-05-08
