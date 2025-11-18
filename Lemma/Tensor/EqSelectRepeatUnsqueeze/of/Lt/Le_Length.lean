import Lemma.List.Lt_LengthInsertIdx
import Lemma.Tensor.SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Tensor.SEqSelectUnsqueeze.of.Le_Length
import Lemma.Nat.EqMod_1'0
open List Tensor Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : d ≤ s.length)
  (h_i : i < n)
  (X : Tensor α s) :
-- imply
  have h_d : d < (s.insertIdx d 1).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h_d]
    omega
  ((X.unsqueeze d).repeat n ⟨d, h_d⟩).select ⟨d, by simpa⟩ ⟨i, by simp_all⟩ ≃ X := by
-- proof
  intros
  let s' := s.insertIdx d 1
  let d' : Fin s'.length := ⟨d, by simpa⟩
  have h_i : i < n * s'[d'] := by
    simpa [s', d']
  have h := SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet h_i (X.unsqueeze d)
  simp [d', s'] at h
  apply h.trans
  simp [EqMod_1'0]
  apply SEqSelectUnsqueeze.of.Le_Length h_d


-- created on 2025-10-05
-- updated on 2025-10-07
