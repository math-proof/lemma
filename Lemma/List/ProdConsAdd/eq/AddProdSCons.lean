import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.Nat.MulAdd.eq.AddMulS
open List Nat


@[main, comm]
private lemma main
  [Mul α] [One α] [Add α] [RightDistribClass α]
-- given
  (s : List α)
  (m n : α) :
-- imply
  ((m + n) :: s).prod = (m :: s).prod + (n :: s).prod := by
-- proof
  repeat rw [ProdCons.eq.Mul_Prod]
  rw [MulAdd.eq.AddMulS]


-- created on 2025-11-02
