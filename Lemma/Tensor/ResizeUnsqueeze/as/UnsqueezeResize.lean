import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Lemma.List.SetInsertIdx.eq.InsertIdxSet.of.GtLength
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
open Bool List Tensor


@[main, comm, cast]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.unsqueeze d).resize ⟨d + 1, by rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength (by grind)]; grind⟩ n ≃ (X.resize d n).unsqueeze d := by
-- proof
  induction s generalizing n with
  | nil =>
    exact Fin.elim0 d
  | cons s₀ s ih =>
    have h_s := SetInsertIdx.eq.InsertIdxSet.of.GtLength (i := d) (n := n) (s := s₀ :: s) (by grind) 1
    apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by grind) h_s
    intro t
    have h_t := t.isLt
    rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
    apply SEqCast.of.SEq.Eq (by simp)
    simp
    match h_d : d with
    | ⟨0, h_lt⟩ =>
      simp
      repeat erw [EqGetUnsqueeze_0.fin]
    | ⟨d + 1, h_d⟩ =>
      rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by simp)]
      simp
      erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
      simp
      erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by grind) (by grind)]
      apply ih (X.get t) ⟨d, by grind⟩ n


-- created on 2026-07-12
-- updated on 2026-07-13
