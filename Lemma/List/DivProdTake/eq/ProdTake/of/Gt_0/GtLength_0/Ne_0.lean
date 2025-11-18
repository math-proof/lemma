import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.Nat.EqDivMul.of.Ne_0
open List Nat


@[main]
private lemma main
  [MonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s[i] ≠ 0) :
-- imply
  (s.take (i + 1)).prod / s[i] = (s.take i).prod := by
-- proof
  simp [ProdTake.eq.MulProdTake.of.Lt_Length i.isLt]
  rwa [EqDivMul.of.Ne_0]


-- created on 2025-11-17
