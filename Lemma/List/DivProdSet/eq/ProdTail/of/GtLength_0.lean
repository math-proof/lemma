import Lemma.List.ProdSet_0.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.EqDivMul.of.Ne_0
open List Nat


@[main]
private lemma main
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {s : List α}
-- given
  (h : s.length > 0)
  (h₁ : a ≠ 0) :
-- imply
  (s.set 0 a).prod / a = s.tail.prod := by
-- proof
  rw [ProdSet_0.eq.Mul_ProdTail.of.GtLength_0 h a]
  rwa [EqDivMul.of.Ne_0.left]


-- created on 2025-07-18
