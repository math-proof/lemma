import Lemma.Tensor.Dot_T.as.Dot
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetGetSlice.eq.Get
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
  (k : ℕ)
  (j : Fin ((⟨0, k, 1⟩ : Slice).length n)) :
-- imply
  (Q @ K[:k]ᵀ)[j] ≃ Q @ K[j]'(by
    have h_j := j.isLt
    simp [List.LengthSlice.eq.Min] at h_j
    grind) := by
-- proof
  apply (SEqGetS.of.SEq.GtLength j.isLt (Dot_T.as.Dot Q K[:k])).trans
  apply Bool.SEq.of.Eq
  simp [GetElem.getElem]
  erw [GetDot.eq.DotGet.une.fin]
  erw [GetGetSlice.eq.Get.fin]
  apply Dot.comm


-- created on 2026-08-17
-- updated on 2026-08-19
