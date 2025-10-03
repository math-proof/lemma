import Lemma.Algebra.Any_Eq_AddMul
import Lemma.Vector.Get.eq.GetFlatten_AddMul
import Lemma.Algebra.LtVal
import Lemma.List.GetVal.eq.Get.of.Lt
import Lemma.Algebra.Add
import Lemma.Vector.GetAdd.eq.AddGetS.of.Lt_Length
open Algebra Vector List


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
