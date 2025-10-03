import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
open Algebra List


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
  apply Mul.gt.Zero.of.Gt_0.Gt_0
  repeat assumption


-- created on 2025-07-12
