import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.Lt_Length
import Lemma.Nat.MulMul.eq.Mul_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s.prod = s[i] * (s.eraseIdx i).prod := by
-- proof
  rw [EraseIdx.eq.Append_Drop_Add_1]
  rw [ProdAppend.eq.MulProdS]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul_ProdTake.eq.ProdTake.of.Lt_Length]
  apply Prod.eq.MulProdS


-- created on 2025-11-03
