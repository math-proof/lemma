import stdlib.SEq
import Lemma.List.Lt_LengthInsertIdx
import Lemma.Tensor.SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.Tensor.SEqSelectUnsqueeze.of.GeLength
import Lemma.Nat.EqMod_1'0
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
import Lemma.List.GetSet.eq.Get.of.Lt.GtLength
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import sympy.tensor.tensor
open List Nat Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d - 1])
  (h_k : k < d)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  ((X.unsqueeze k).repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ ((X.select ⟨d - 1, by omega⟩ ⟨i, by simpa⟩).unsqueeze k).repeat n ⟨k, by grind⟩ := by
-- proof
  let s' := s.insertIdx d 1
  let d' : Fin s'.length := ⟨d, by simp [s']; grind⟩
  -- have h := SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet (by grind) (X.unsqueeze d)
  sorry


-- created on 2025-11-17
