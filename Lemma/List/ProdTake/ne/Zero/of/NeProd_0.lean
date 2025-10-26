import Lemma.Nat.Ne_0.of.Mul.ne.Zero
import Lemma.List.Prod.eq.MulProdDrop__ProdTake
open List Nat


@[main]
private lemma main
  [CommMonoidWithZero α]
  {s : List α}
-- given
  (h : s.prod ≠ 0) 
  (i : ℕ):
-- imply
  (s.take i).prod ≠ 0 := by
-- proof
  rw [Prod.eq.MulProdDrop__ProdTake s i] at h
  apply Ne_0.of.Mul.ne.Zero h


-- created on 2025-09-23
