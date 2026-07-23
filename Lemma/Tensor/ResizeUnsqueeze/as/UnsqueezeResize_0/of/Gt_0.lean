import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.InsertIdx.eq.Cons_InsertIdxTail.of.Gt_0.GtLength_0
import Lemma.List.Lt0LengthInsertIdx.of.GeLength
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqUnsqueeze0'0
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.Resize_0.as.AppendCast_Repeat_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEq0S.of.Eq
import Lemma.Tensor.UnsqueezeCast.as.Unsqueeze.of.Eq
open Bool List Nat Tensor
set_option maxHeartbeats 1000000


@[main, comm, cast]
private lemma main
  [Zero α]
-- given
  (h_s : d ≤ s.length)
  (h_d : d > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.unsqueeze d).resize ⟨0, Lt0LengthInsertIdx.of.GeLength h_s 1⟩ n ≃ (X.resize ⟨0, by grind⟩ n).unsqueeze d := by
-- proof
  simp
  apply SEq.of.All_SEqGetS.Eq.GtLength_0
  ·
    intro i
    have h_i := i.isLt
    have h_InsertIdx := InsertIdx.eq.Cons_InsertIdxTail.of.Gt_0.GtLength_0 (s := s) (by grind) h_d 1
    simp [h_InsertIdx] at h_i
    conv_lhs => erw [Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 (by grind)]
    conv_lhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := (s.insertIdx d 1).set 0 n) (i := ⟨i, by simpa [h_InsertIdx, EqAddMulDiv]⟩) (by grind) (by simp [h_InsertIdx, EqAddMulDiv])]
    conv_rhs => erw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind)]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [EqAddMulDiv]
      rw [TailSet_0.eq.Tail]
    ·
      rw [InsertIdx.eq.Cons_InsertIdxTail.of.Gt_0.GtLength_0 (s := s.set 0 n) (by grind) h_d]
      simp
    ·
      conv_rhs => erw [Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 (by grind)]
      conv_rhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := s.set 0 n) (i := ⟨i, by simp [EqAddMulDiv]; grind⟩) (by grind) (by rw [EqAddMulDiv, Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)])]
      simp
      if h_lt : i < n / s[0] * s[0] then
        rw [GetAppend.eq.Get.of.Lt.fin (by simpa [h_InsertIdx])]
        conv_lhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := n / (s.insertIdx d 1)[0]'(by grind) * (s.insertIdx d 1)[0]'(by grind) :: (s.insertIdx d 1).tail) (i := ⟨i, by grind⟩) (by grind) (by simp [h_InsertIdx])]
        conv_rhs => erw [UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq (by rw [EqAddMulDiv, Set_0.eq.Cons_Tail.of.GtLength_0 (h := by grind)])]
        apply SEqCastS.of.SEq.Eq.Eq (by simp [h_InsertIdx])
        ·
          congr 1
          simp [TailSet_0.eq.Tail]
        ·
          simp
          rw [GetAppend.eq.Get.of.Lt.fin h_lt]
          conv_rhs => erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := (n / s[0] * s[0] :: s.tail)) (i := ⟨i, by grind⟩) (by grind) (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (h := by grind)]; grind)]
          rw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin]
          conv_rhs => erw [UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (h := by grind)]; grind)]
          apply SEqCastS.of.SEq.Eq.Eq (by simp [h_InsertIdx])
          ·
            simp [TailSet_0.eq.Tail]
          ·
            simp [h_InsertIdx]
            rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by grind) h_d (Nat.mod_lt i.val (Gt_0.of.GtMul (Nat.zero_lt_of_lt h_lt)))]
            rw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
            conv_rhs => erw [UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind)]
            apply SEqCastS.of.SEq.Eq.Eq (by simp [h_InsertIdx]) (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind) (by rfl)
            grind
          ·
            grind
      else
        rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin]
        ·
          simp [h_InsertIdx]
          rw [EqGet0_0.fin]
          conv_rhs => erw [UnsqueezeCast.eq.Cast_Unsqueeze.of.Eq (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind)]
          apply SEq_Cast.of.SEq.Eq (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]; grind)
          rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin]
          ·
            rw [EqGet0_0.fin]
            conv_rhs => erw [EqUnsqueeze0'0]
            apply SEq0S.of.Eq
            grind
          ·
            grind
        ·
          simp [h_InsertIdx]
          grind
  ·
    have h_InsertIdx := InsertIdx.eq.Cons_InsertIdxTail.of.Gt_0.GtLength_0 (s := s) (by grind) h_d 1
    have h_InsertIdx2 := InsertIdx.eq.Cons_InsertIdxTail.of.Gt_0.GtLength_0 (s := s.set 0 n) (by grind) h_d 1
    simp [h_InsertIdx, h_InsertIdx2, Set_0.eq.Cons_Tail.of.GtLength_0, TailSet_0.eq.Tail]


-- created on 2026-07-13
-- updated on 2026-07-14
