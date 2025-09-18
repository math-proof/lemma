import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main, comm]
private lemma main
  [Field α]
  (x y a : α) :
-- imply
  (x + y) / a = x / a + y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [AddMulS.eq.MulAdd]



-- created on 2024-07-01
