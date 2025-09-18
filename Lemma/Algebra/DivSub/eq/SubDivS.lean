import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.MulSub.eq.SubMulS
open Algebra


@[main, comm]
private lemma main
  [Field α]
  {x y a : α} :
-- imply
  (x - y) / a = x / a - y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.MulSub]


-- created on 2025-03-02
