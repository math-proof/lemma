import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [One α] [CommMagma α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.drop i).prod = (s.drop (i + 1)).prod * s[i] := by
-- proof
  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h]
  rw [Mul.comm]


-- created on 2025-10-23
