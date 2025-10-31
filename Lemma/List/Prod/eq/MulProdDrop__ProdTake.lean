import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Nat.Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.drop i).prod * (s.take i).prod := by
-- proof
  rw [Prod.eq.MulProdTake__ProdDrop s i]
  apply Mul.comm


-- created on 2025-07-12
