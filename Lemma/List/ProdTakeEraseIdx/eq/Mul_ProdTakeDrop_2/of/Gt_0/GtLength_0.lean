import Lemma.List.ProdTakeEraseIdx.eq.Mul_ProdTakeDrop_2.of.GtLength_0
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_d : d > 0) :
-- imply
  ((s.eraseIdx 1).take d).prod = s[0] * ((s.drop 2).take (d - 1)).prod := by
-- proof
  have := ProdTakeEraseIdx.eq.Mul_ProdTakeDrop_2.of.GtLength_0 h_s (d - 1)
  rwa [EqAddSub.of.Ge (by omega)] at this


-- created on 2025-11-04
