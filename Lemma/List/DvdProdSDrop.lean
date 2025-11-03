import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid Z]
-- given
  (s : List Z)
  (i d : ℕ) :
-- imply
  (s.drop (i + d)).prod ∣ (s.drop i).prod := by
-- proof
  rw [ProdDrop.eq.MulProdS s i d]
  apply Dvd_Mul


-- created on 2025-11-03
