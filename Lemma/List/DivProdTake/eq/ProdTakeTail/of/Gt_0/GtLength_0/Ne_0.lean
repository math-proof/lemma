import Lemma.List.ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0
import Lemma.Nat.EqDivMul.of.Ne_0
open List Nat


@[main]
private lemma main
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > 0)
  (h_i : i > 0)
  (h_0 : s[0] ≠ 0) :
-- imply
  (s.take i).prod / s[0] = (s.tail.take (i - 1)).prod := by
-- proof
  rw [ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0 h h_i]
  rw [EqDivMul.of.Ne_0.left h_0]


-- created on 2025-07-05
