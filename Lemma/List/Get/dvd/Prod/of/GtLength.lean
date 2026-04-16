import Lemma.List.Get.dvd.ProdDrop.of.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Dvd_Mul.of.Dvd
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i] ∣ s.prod := by
-- proof
  rw [Prod.eq.MulProdS s i]
  apply Dvd_Mul.of.Dvd
  apply Get.dvd.ProdDrop.of.GtLength h


-- created on 2026-04-16
