import stdlib.SEq
import sympy.tensor.functions
import Lemma.Tensor.GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq
import Lemma.Bool.EqCast.of.SEq.Eq
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.Nat.LtVal
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.Tensor.GetEllipsisRepeat.as.GetEllipsis_Mod_Get.of.Lt_MulGet
import Lemma.Tensor.SEqGetEllipsisUnsqueeze.of.Le_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
open Tensor List Bool Nat


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List ℕ}
  {dim : Fin s.length}
-- given
  (h : s[dim] > 0)
  (X : Tensor α s) :
-- imply
  X.sum dim = (X.sum_keepdim dim).getEllipsis dim ⟨0, h⟩ := by
-- proof
  unfold Tensor.sum_keepdim
  have h_lt := LtVal dim
  have h_dim := Lt_LengthInsertIdxEraseIdx.of.Lt_Length h_lt 1
  have h_cast := GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq
    (by simp [EqSetInsertIdxEraseIdx.of.Lt_Length])
    ((((X.sum dim).unsqueeze dim).repeat s[dim] ⟨dim, h_dim⟩)) ⟨dim, by simpa⟩ ⟨0, by simpa⟩
    (s' := s)
  simp at h_cast
  simp [h_cast]
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  ·
    have h := GetEllipsisRepeat.as.GetEllipsis_Mod_Get.of.Lt_MulGet (by simpa) ((X.sum dim).unsqueeze dim) (i := 0) (dim := ⟨dim, by simpa⟩)
    apply SEq.symm ∘ h.trans
    apply SEqGetEllipsisUnsqueeze.of.Le_Length
    rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_lt]
    omega


-- created on 2025-10-05
-- updated on 2025-10-07
