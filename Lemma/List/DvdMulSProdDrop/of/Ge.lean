import Lemma.List.DvdProdSDrop.of.Ge
import Lemma.Nat.DvdMulS.of.Dvd
open List Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (h : i ≥ j)
  (s : List α)
  (n : α) :
-- imply
  (s.drop i).prod * n ∣ (s.drop j).prod * n:= by
-- proof
  apply DvdMulS.of.Dvd
  apply DvdProdSDrop.of.Ge h


-- created on 2025-11-29
