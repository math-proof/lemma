import Lemma.List.DvdProdSDrop.of.Ge
import Lemma.Nat.DvdMulS.of.Dvd
open Nat List


@[main]
private lemma main
  [CommMonoid α]
-- given
  (h : i ≥ j)
  (s : List α)
  (n : α) :
-- imply
  n * (s.drop i).prod ∣ n * (s.drop j).prod := by
-- proof
  apply DvdMulS.of.Dvd.left
  apply DvdProdSDrop.of.Ge h


-- created on 2025-11-29
