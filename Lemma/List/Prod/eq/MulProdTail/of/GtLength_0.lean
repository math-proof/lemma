import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Mul
open List Nat


@[main]
private lemma main
  [One α] [CommMagma α]
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v.prod = v.tail.prod * v[0] := by
-- proof
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
  apply Mul.comm


-- created on 2025-10-20
