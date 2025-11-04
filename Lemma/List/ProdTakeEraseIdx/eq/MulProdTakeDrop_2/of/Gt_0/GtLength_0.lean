import Lemma.List.ProdTakeEraseIdx.eq.Mul_ProdTakeDrop_2.of.Gt_0.GtLength_0
import Lemma.Nat.Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_d : d > 0) :
-- imply
  ((s.eraseIdx 1).take d).prod = ((s.drop 2).take (d - 1)).prod * s[0] := by
-- proof
  rw [ProdTakeEraseIdx.eq.Mul_ProdTakeDrop_2.of.Gt_0.GtLength_0 h_s h_d]
  apply Mul.comm


-- created on 2025-11-04
