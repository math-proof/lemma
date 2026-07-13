import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Eq_0
import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Lemma.List.SetInsertIdx_Succ.eq.InsertIdxSet.of.GtLength
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetDite.eq.Get.of.Not
import Lemma.Tensor.GetDite.eq.Get.of.Cond
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.GtLength_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.Resize_0.as.AppendCast_Repeat_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
open Bool Fin List Tensor
set_option maxHeartbeats 2000000


@[main, comm, cast]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.unsqueeze d.succ).resize ⟨d, by rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength (by grind)]; grind⟩ n ≃ (X.resize d n).unsqueeze d.succ := by
-- proof
  induction s generalizing n with
  | nil =>
    exact Fin.elim0 d
  | cons s₀ s ih =>
    have h_s := SetInsertIdx_Succ.eq.InsertIdxSet.of.GtLength (i := d) (n := n) (s := s₀ :: s) (by grind) 1
    apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by grind) h_s
    intro t
    have h_t := t.isLt
    erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.GtLength_0.fin (by grind) (by grind)]
    apply SEq_Cast.of.SEq.Eq (by simp; sorry)
    simp
    match h_d : d with
    | ⟨0, h_lt⟩ =>
      simp
      apply SEq.of.All_SEqGetS.Eq.Eq (by rfl) (by rfl)
      intro i
      have h_i := Eq_0 i
      subst h_i
      simp [GetElem.getElem]
      erw [EqGetUnsqueeze_0.fin]
      erw [Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 (by grind)]
      conv_rhs => erw [Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 (by grind)]
      sorry
    | ⟨d + 1, h_d⟩ =>
      simp
      erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (d := ⟨d + 1, by grind⟩) (by grind) (by grind)]
      conv_rhs => erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (d := ⟨d + 1, by grind⟩) (by grind) (by grind)]
      simp
      erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
      simp
      apply ih (X.get t) ⟨d, by grind⟩ n


-- created on 2026-07-13
