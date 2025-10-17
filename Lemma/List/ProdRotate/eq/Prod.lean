import stdlib.List
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.Prod.eq.MulProdDrop__ProdTake
open List


@[main]
private lemma main
  [CommMonoid α]
-- given
  (a : List α)
  (i : ℕ) :
-- imply
  (a.rotate i).prod = a.prod := by
-- proof
  rw [Rotate.eq.AppendDrop__Take]
  rw [Prod.eq.MulProdDrop__ProdTake a (i % a.length)]
  simp


-- created on 2025-10-17
