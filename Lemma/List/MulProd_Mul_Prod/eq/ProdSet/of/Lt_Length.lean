import Lemma.List.ProdSet.eq.MulMulProd__Prod.of.Lt_Length
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
import Lemma.List.ProdCons.eq.Mul_Prod
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : d < s.length)
  (n : α) :
-- imply
  ((s.take d).prod * (n * (s.drop d).prod)) = (s.set d (n * s[d])).prod := by
-- proof
  rw [ProdSet.eq.MulMulProd__Prod.of.Lt_Length h (n * s[d])]
  rw [MulMul.eq.Mul_Mul]
  apply EqMulS.of.Eq.left
  rw [MulMul.eq.Mul_Mul]
  apply EqMulS.of.Eq.left
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length h]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-07-17
