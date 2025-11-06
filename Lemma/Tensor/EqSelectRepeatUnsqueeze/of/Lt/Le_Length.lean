import sympy.tensor.tensor
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
  (h_dim : dim ≤ s.length)
  (h_i : i < n)
  (X : Tensor α s) :
-- imply
  have h_dim : dim < (s.insertIdx dim 1).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h_dim]
    omega
  ((X.unsqueeze dim).repeat n ⟨dim, h_dim⟩).select ⟨dim, by simpa⟩ ⟨i, by simp_all⟩ ≃ X := by
-- proof
  intros
  let s' := s.insertIdx dim 1
  let dim' : Fin s'.length := ⟨dim, by simpa⟩
  have h_i : i < n * s'[dim'] := by
    simpa [s', dim']
  have h := SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet h_i (X.unsqueeze dim)
  simp [dim', s'] at h
  apply h.trans
  simp [EqMod_1'0]
  apply SEqSelectUnsqueeze.of.Le_Length h_dim


-- created on 2025-10-05
-- updated on 2025-10-07
