import Lemma.Tensor.GetTranspose.as.TransposeGet
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.Gt_0.GtLength
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Eq_Fin
import Lemma.List.InsertIdxAppend.eq.Append_Cons
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.Slice.eq.Nil
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
open Bool Fin List Nat Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α ((b :: bz) ++ [m, k]))
  (Y : Tensor α ((b :: bz) ++ [k, n]))
  (i : Fin b) :
-- imply
  (X.batch_dot Y)[i] = X[i].batch_dot Y[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.batch_dot]
  apply Eq_Cast.of.SEq.Eq (by grind)
  conv_lhs => rw [Eq_Fin i]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) (by simp; grind)]
  apply SEqCast.of.SEq.Eq (by simp; grind)
  apply SEq.of.Eq
  rw [GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.GtLength.fin (by grind) (by grind) (by grind)]
  apply EqSumS.of.Eq
  erw [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind)]
  have h_s : (b :: bz ++ [m, k]).insertIdx ((b :: bz).length + 1) 1 = b :: bz ++ [m, 1, k] := by simp [List.InsertIdxAppend.eq.Append_InsertIdx]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := b :: (bz ++ [m, n, k]))
    (by grind)
    (by grind)
    ((cast (congrArg (Tensor α) h_s) (X.unsqueeze (bz.length + 1 + 1))).repeat n ⟨bz.length + 1 + 1, by grind⟩)
    ⟨i, by grind⟩
  simp at this
  simp [this]
  conv_lhs =>
    arg 2
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by grind) (by grind)]
  have h_s₁ : (b :: bz ++ [m, k]).insertIdx ((b :: bz).length + 1) 1 = b :: bz ++ [m, 1, k] := by
    simp [InsertIdxAppend.eq.Append_InsertIdx]
  have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtLength_0.fin
    (i := i)
    (by grind)
    (by simp)
    (cast (congrArg (Tensor α) h_s₁) (X.unsqueeze (bz.length + 1 + 1)))
    n
    ⟨bz.length + 1, by grind⟩
  simp at this
  simp [this]
  have h_s_t₁ : (b :: bz ++ [n, k]).insertIdx (b :: bz).length 1 = b :: bz ++ [1, n, k] := by
    simp [InsertIdxAppend.eq.Append_Cons]
  have h_s_t₂ : (b :: bz ++ [k, n]).swap ((b :: bz ++ [k, n]).length - 2) ((b :: bz ++ [k, n]).length - 1) = b :: bz ++ [n, k] := by
    simp [List.swap, AddAdd.eq.Add_Add, Slice.eq.Nil]
  have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtLength_0.fin
    (i := i)
    (by grind)
    (by simp)
    (cast (congrArg (Tensor α) h_s_t₁) ((cast (congrArg (Tensor α) h_s_t₂) Yᵀ).unsqueeze (bz.length + 1)))
    m
    ⟨bz.length, by grind⟩
  simp at this
  simp [this]
  conv_lhs => rw [Eq_Fin i]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (s' := b :: bz ++ [m, 1, k]) (by grind) (by grind)]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (s' := b :: bz ++ [1, n, k]) (by grind) (by grind)]
  have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.GtLength_0.fin
    (i := i)
    (by grind)
    (by grind)
    X
    (bz.length + 1)
  simp at this
  simp [this]
  apply EqMulS.of.Eq.left
  apply EqCastS.of.SEq.Eq.left (by grind)
  apply SEq.of.Eq
  apply EqRepeatS.of.Eq
  apply EqCastS.of.SEq.Eq.left (by grind)
  apply SEq.of.Eq
  have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.GtLength_0.fin
    (i := i)
    (by grind)
    (by grind)
    (cast (congrArg (Tensor α) h_s_t₂) Yᵀ)
    (bz.length)
  simp at this
  simp [this]
  conv_lhs => rw [Eq_Fin i]
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (s' := (b :: bz ++ [n, k])) (by grind) (by grind)]
  simp
  apply EqUnsqueezeS.of.Eq
  apply EqCastS.of.SEq.Eq.left (by grind)
  apply GetTranspose.as.TransposeGet


-- created on 2026-06-24
-- updated on 2026-07-03
