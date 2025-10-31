import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Mul
open List Nat


@[main]
private lemma main
  [One α] [CommMagma α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.prod = s.tail.prod * s[0] := by
-- proof
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
  apply Mul.comm


-- created on 2025-10-20
