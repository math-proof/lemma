import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetMul.eq.MulGetS.of.GtLength
open Vector Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.FlattenMul.eq.MulFlattenS |
| comm | Vector.MulFlattenS.eq.FlattenMul |
-/
@[path, comm]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  (a * b).flatten = a.flatten * b.flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul k.isLt
  have hk := k.isLt
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  rw [GetMul.eq.MulGetS.of.GtLength]
  repeat rw [GetFlatten_AddMul.eq.Get]
  simp [GetMul.eq.MulGetS.of.GtLength]


-- created on 2025-07-03
-- updated on 2026-11-20
