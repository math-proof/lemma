import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [One α] [CommMagma α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.drop i).prod = (v.drop (i + 1)).prod * v[i] := by
-- proof
  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length h]
  rw [Mul.comm]


-- created on 2025-10-23
