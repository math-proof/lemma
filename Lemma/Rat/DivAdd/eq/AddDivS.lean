import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Nat.MulAdd.eq.AddMulS
open Nat Rat


@[main, comm]
private lemma main
  [DivInvMonoid α]
  [Add α]
  [RightDistribClass α]
-- given
  (x y a : α) :
-- imply
  (x + y) / a = x / a + y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [AddMulS.eq.MulAdd]


-- created on 2024-07-01
