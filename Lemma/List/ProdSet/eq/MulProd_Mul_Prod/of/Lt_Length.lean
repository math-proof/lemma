import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : i < v.length)
  (a : α) :
-- imply
  (v.set i a).prod = (v.take i).prod * (a * (v.drop (i + 1)).prod) := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h]
  rw [ProdAppend.eq.MulProdS]
  apply EqMulS.of.Eq.left
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-07-12
