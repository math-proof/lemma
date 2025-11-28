import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.drop (i + 1)).prod ∣ ((s.eraseIdx i).drop j).prod := by
-- proof
  rw [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge h]
  apply Dvd_Mul


-- created on 2025-11-21
