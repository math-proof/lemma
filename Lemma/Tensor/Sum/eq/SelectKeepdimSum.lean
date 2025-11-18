import sympy.tensor.functions
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.Tensor.SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet
import Lemma.Tensor.SEqSelectUnsqueeze.of.Le_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
open Tensor List Bool Nat


@[main, comm]
private lemma main
  [Add α] [Zero α]
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  X.sum d = (X.sum d).keepdim.select d i := by
-- proof
  unfold Tensor.keepdim
  simp
  have h_d := d.isLt
  have h_dim := Lt_LengthInsertIdxEraseIdx.of.Lt_Length h_d 1
  have h_cast := SelectCast.eq.Cast_Select.of.Eq
    (by simp [EqSetInsertIdxEraseIdx.of.Lt_Length])
    ((((X.sum d).unsqueeze d).repeat s[d] ⟨d, h_dim⟩)) ⟨d, by simpa⟩ ⟨i, by simp⟩
    (s' := s)
  simp at h_cast
  simp [h_cast]
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length]
  ·
    have h := SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet (by simp) ((X.sum d).unsqueeze d) (i := i) (d := ⟨d, by simpa⟩) (n := s[d])
    apply SEq.symm ∘ h.trans
    simp [EqMod_1'0] at *
    apply SEqSelectUnsqueeze.of.Le_Length
    rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_d]
    omega


-- created on 2025-10-05
-- updated on 2025-10-07
