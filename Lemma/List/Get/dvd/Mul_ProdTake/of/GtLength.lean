import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.Nat.Dvd_Mul.of.Dvd
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (n : α) :
-- imply
  s[i] ∣ n * (s.take (i + 1)).prod := by
-- proof
  apply Dvd_Mul.of.Dvd
  apply Get.dvd.ProdTake.of.GtLength h


-- created on 2025-11-30
