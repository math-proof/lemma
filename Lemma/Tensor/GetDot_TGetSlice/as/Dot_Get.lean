import Lemma.Tensor.Dot_T.as.Dot
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetDot_TGetSlice.as.Dot_Get |
| fin | Tensor.GetDot_TGetSlice.as.Dot_Get.fin |
-/
@[main, fin]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (Q : Tensor α [d])
  (K : Tensor α [n, d])
  (start stop : ℕ)
  (j : Fin ((⟨start, stop, 1⟩ : Slice).length n)) :
-- imply
  (Q @ K[start:stop]ᵀ)[j] ≃ Q @ K[start + j]'(by
    have h_j := j.isLt
    simp [List.LengthSlice.eq.SubMin] at h_j
    grind) := by
-- proof
  apply (SEqGetS.of.SEq.GtLength j.isLt (Dot_T.as.Dot Q K[start:stop])).trans
  apply Bool.SEq.of.Eq
  simp [GetElem.getElem]
  erw [GetDot.eq.DotGet.une.fin]
  have h_j := j.isLt
  simp [List.LengthSlice.eq.SubMin] at h_j
  erw [GetGetSlice.eq.Get_Add.of.GtSubMin.fin h_j]
  apply Dot.comm


@[main, fin]
private lemma zero
  [CommMagma α] [AddCommMonoid α]
-- given
  (Q : Tensor α [d])
  (K : Tensor α [n, d])
  (k : ℕ)
  (j : Fin ((⟨0, k, 1⟩ : Slice).length n)) :
-- imply
  (Q @ K[:k]ᵀ)[j] ≃ Q @ K[j]'(by
    have h_j := j.isLt
    simp [List.LengthSlice.eq.Min] at h_j
    grind) := by
-- proof
  apply SEq.trans (b := Q @ K[(0 : ℕ) + j]'(by
    have h_j := j.isLt
    simp [List.LengthSlice.eq.Min] at h_j
    grind))
  ·
    apply main (start := 0) (stop := k)
  ·
    apply Bool.SEq.of.Eq
    simp
    rfl


-- created on 2026-08-17
-- updated on 2026-08-20
