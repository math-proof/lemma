import Lemma.Nat.Any_Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Nat.LtVal
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Nat.Add
import Lemma.Vector.GetAdd.eq.AddGetS.of.Lt_Length
open Vector Nat


@[main]
private lemma main
  [Add α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  a.flatten + b.flatten = (a + b).flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul k
  have hk := LtVal k
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  rw [GetAdd.eq.AddGetS.of.Lt_Length]
  repeat rw [GetFlatten_AddMul.eq.Get]
  simp [GetAdd.eq.AddGetS.of.Lt_Length]


-- created on 2025-07-20
-- updated on 2025-09-24
