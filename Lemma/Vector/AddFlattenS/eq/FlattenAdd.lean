import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetAdd.eq.AddGetS.of.GtLength
open Vector Nat


@[path]
private lemma main
  [Add α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  a.flatten + b.flatten = (a + b).flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul k.isLt
  have hk := k.isLt
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  rw [GetAdd.eq.AddGetS.of.GtLength]
  repeat rw [GetFlatten_AddMul.eq.Get]
  simp [GetAdd.eq.AddGetS.of.GtLength]


-- created on 2025-07-20
-- updated on 2026-11-20
