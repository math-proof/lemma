import Lemma.Nat.Any_Eq_AddMul
import Lemma.Nat.Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetMul.eq.MulGetS.of.GtLength
open Vector Nat


@[main, comm]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  (a * b).flatten = a.flatten * b.flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul k
  have hk := k.isLt
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  rw [GetMul.eq.MulGetS.of.GtLength]
  repeat rw [GetFlatten_AddMul.eq.Get]
  simp [GetMul.eq.MulGetS.of.GtLength]


-- created on 2025-07-03
-- updated on 2025-09-24
