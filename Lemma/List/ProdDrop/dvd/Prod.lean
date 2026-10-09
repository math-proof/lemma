import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Dvd_Mul
open List Nat


@[path]
private lemma main
  [CommMonoid α]
-- given
  (s : List α)
  (d : ℕ) :
-- imply
  (s.drop d).prod ∣ s.prod := by
-- proof
  rw [Prod.eq.MulProdS s d]
  apply Dvd_Mul


-- created on 2025-07-09
-- updated on 2025-11-24
