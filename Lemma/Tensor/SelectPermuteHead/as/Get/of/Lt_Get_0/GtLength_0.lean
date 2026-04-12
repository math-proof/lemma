import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.GtLength
import Lemma.List.EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.GeLength
import Lemma.List.GetRotate.eq.Get_0.of.Gt_0.GeLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.TakeRotate.eq.Tail
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool List Tensor Vector


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
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩) h_s]
    ·
      rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
        rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength]
        ·
          grind
        ·
          rwa [GetRotate.eq.Get_0.of.Gt_0.GeLength (by grind) (by grind)]
      ·
        simp
      ·
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := t.isLt
          sorry
        ·
          simp
          rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength]
          ·
            rw [Drop.eq.Nil.of.LeLength (by grind)]
            simp [TakeRotate.eq.Tail]
          ·
            rwa [GetRotate.eq.Get_0.of.Gt_0.GeLength (by grind) (by grind)]
    ·
      assumption


-- created on 2026-04-09
-- updated on 2026-04-12
