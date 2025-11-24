import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (d : ℕ) :
-- imply
  (s.take d).prod ∣ s.prod := by
-- proof
  rw [Prod.eq.MulProdS s d]
  apply Dvd_Mul.left


-- created on 2025-11-24
