import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
open List Nat


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulStrictMono α] 
  [One α]
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_0 : s[0] > 0)
  (h_tail : s.tail.prod > 0) :
-- imply
  s.prod > 0 := by
-- proof
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]
  apply Lt0Mul.of.Gt_0.Gt_0
  repeat assumption


-- created on 2025-07-12
