import Lemma.Algebra.Any_Eq_AddMul
import Lemma.Nat.Mul
import Lemma.Vector.Get.eq.GetFlatten_AddMul
import Lemma.Algebra.LtVal
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetMul.eq.MulGetS.of.Lt_Length
open Algebra Vector Nat


@[main]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector (List.Vector α n) m) :
-- imply
  a.flatten * b.flatten = (a * b).flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul k
  have hk := LtVal k
  simp [List.Vector.get]
  rw [GetVal.eq.Get.of.Lt hk]
  rw [GetVal.eq.Get.of.Lt hk]
  simp [h_eq]
  rw [GetMul.eq.MulGetS.of.Lt_Length]
  repeat rw [GetFlatten_AddMul.eq.Get]
  simp [GetMul.eq.MulGetS.of.Lt_Length]


-- created on 2025-07-03
-- updated on 2025-09-24
