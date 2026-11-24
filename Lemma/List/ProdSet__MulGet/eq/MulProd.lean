import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Theorem.List.Prod.eq.MulProdS
open List


@[path]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (t : α) :
-- imply
  (s.set i (s[i] * t)).prod = s.prod * t := by
-- proof
  rw [List.prod_set]
  simp
  rw [Prod.eq.MulProdS s i, ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength i.isLt]
  ac_rfl


-- created on 2025-06-08
-- updated on 2026-11-20
