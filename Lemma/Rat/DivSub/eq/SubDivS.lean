import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Int.MulSub.eq.SubMulS
open Int Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {x y a : α} :
-- imply
  (x - y) / a = x / a - y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.MulSub]


-- created on 2025-03-02
