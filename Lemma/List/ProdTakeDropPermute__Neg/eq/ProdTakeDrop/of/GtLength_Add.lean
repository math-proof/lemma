import Lemma.List.ProdTakeDrop.eq.Mul_ProdTakeDrop.of.GtLength_Add
import Lemma.List.ProdTakeDropPermute__Neg.eq.Mul_ProdTakeDrop.of.GtLength_Add
open List


@[main, comm]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (((s.permute ⟨i + d, h⟩ (-d)).drop i).take (d + 1)).prod = ((s.drop i).take (d + 1)).prod := by
-- proof
  simp [ProdTakeDropPermute__Neg.eq.Mul_ProdTakeDrop.of.GtLength_Add h]
  rw [ProdTakeDrop.eq.Mul_ProdTakeDrop.of.GtLength_Add h]


-- created on 2025-10-29
