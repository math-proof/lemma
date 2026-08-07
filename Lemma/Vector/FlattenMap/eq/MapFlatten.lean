import Lemma.Nat.Any_Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetVal.eq.Get.of.Lt
open Nat Vector


@[main, comm]
private lemma main
  {f : α → β}
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (v.map fun row => row.map f).flatten = (v.flatten).map f := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul k
  have hk := k.isLt
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  simp [GetFlatten_AddMul.eq.Get]


-- created on 2026-08-07
