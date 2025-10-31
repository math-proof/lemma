import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : i < s.length)
  (a : α) :
-- imply
  (s.set i a).prod = (s.take i).prod * (a * (s.drop (i + 1)).prod) := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h]
  rw [ProdAppend.eq.MulProdS]
  apply EqMulS.of.Eq.left
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-07-12
