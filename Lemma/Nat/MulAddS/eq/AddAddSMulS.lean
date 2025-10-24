import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Mul_Add.eq.AddMulS
open Nat


@[main, comm]
private lemma main
  [Mul α] [Add α] [RightDistribClass α] [LeftDistribClass α]
-- given
  (a b c : α) :
-- imply
  (a + b) * (c + d) = (a * c + a * d) + (b * c + b * d) := by
-- proof
  rw [MulAdd.eq.AddMulS]
  repeat rw [Mul_Add.eq.AddMulS]


-- created on 2025-10-24
