import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (h : i ≤ j)
  (s : List α) :
-- imply
  (s.drop i).prod = ((s.take j).drop i).prod * (s.drop j).prod := by
-- proof
  rw [ProdDrop.eq.MulProdS s i (j - i)]
  rw [TakeDrop.eq.DropTake]
  simp [EqAdd_Sub.of.Ge h]


-- created on 2025-11-21
