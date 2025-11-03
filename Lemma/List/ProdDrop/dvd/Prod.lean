import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
-- given
  (s : List ℕ)
  (d : ℕ) :
-- imply
  (s.drop d).prod ∣ s.prod := by
-- proof
  rw [Prod.eq.MulProdS s d]
  apply Dvd_Mul


-- created on 2025-07-09
