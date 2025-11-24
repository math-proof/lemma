import Lemma.List.ProdTake.eq.Mul_ProdTake.of.Lt_Length
import Lemma.Nat.EqDivMul.of.Ne_0
open List Nat


@[main, comm]
private lemma main
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {s : List α}
-- given
  (h : i < s.length)
  (h_i : s[i] ≠ 0) :
-- imply
  (s.take i).prod = (s.take (i + 1)).prod / s[i] := by
-- proof
  rw [ProdTake.eq.Mul_ProdTake.of.Lt_Length h]
  rw [EqDivMul.of.Ne_0.left]
  grind


-- created on 2025-11-24
