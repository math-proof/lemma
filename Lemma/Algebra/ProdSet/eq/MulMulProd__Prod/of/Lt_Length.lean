import Lemma.Algebra.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.Algebra.ProdAppend.eq.MulProdS
import Lemma.Algebra.ProdCons.eq.Mul_Prod
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : i < v.length)
  (a : α) :
-- imply
  (v.set i a).prod = (v.take i).prod * a * (v.drop (i + 1)).prod := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h]
  rw [ProdAppend.eq.MulProdS]
  rw [MulMul.eq.Mul_Mul]
  apply EqMulS.of.Eq.left
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-07-12
