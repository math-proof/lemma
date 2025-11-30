import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.Nat.DvdMulS.of.Dvd
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (n : α) :
-- imply
  n * s[i] ∣ n * (s.take (i + 1)).prod := by
-- proof
  apply DvdMulS.of.Dvd.left
  apply Get.dvd.ProdTake.of.GtLength h


-- created on 2025-11-30
