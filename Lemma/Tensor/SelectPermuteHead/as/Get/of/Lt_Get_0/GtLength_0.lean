import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.GtLength
import Lemma.List.EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.GeLength
import Lemma.List.GetRotate.eq.Get_0.of.Gt_0.GeLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 0)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permuteHead s.length).select ⟨s.length - 1, by grind⟩ ⟨k, by simp; rwa [GetRotate.eq.Get_0.of.Gt_0.GeLength (by grind) (by grind)]⟩ ≃ X.get ⟨k, by rwa [← Length.eq.Get_0.of.GtLength_0 (by omega) X] at h_k⟩ := by
-- proof
  unfold permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    rw [EraseIdxAppend.eq.AppendEraseIdx.of.GtLength (by grind)]
    simp
    rw [EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.GeLength (by grind) (by grind)]
    simp
    right
    constructor
    repeat grind
  ·
    sorry


-- created on 2026-04-09
-- updated on 2026-04-12
