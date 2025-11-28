import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_k : s.length > k)
  (h_d : d < k) :
-- imply
  ((s.eraseIdx d).take k).prod = ((s.eraseIdx d).take (k - 1)).prod * s[k] := by
-- proof
  have := ProdTake.eq.MulProdTake.of.GtLength (s := s.eraseIdx d) (i := k - 1) (by grind)
  rw [EqAddSub.of.Ge (by omega)] at this
  rw [this]
  rw [GetEraseIdx.eq.Get.of.Lt.GtLength _ h_d]


-- created on 2025-11-28
