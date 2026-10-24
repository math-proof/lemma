import Lemma.Vector.EqHeadSplitAt_0
import torch.Tensor.prod
import Lemma.Vector.Get.of.Eq.Lt
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.DataAppend.as.FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetAppend.eq.Get
open Bool Fin Tensor Vector Set


@[path]
private lemma cons
-- given
  (h : m = 0)
  (X : Tensor α (n :: s))
  (O : Tensor α (m :: s)) :
-- imply
  X ++ O ≃ X := by
-- proof
  subst h
  apply SEq.of.All_SEqGetS.Eq.Eq
  ·
    rfl
  ·
    intro i
    have h_i := i.isLt
    conv_rhs at h_i => simp
    simp [GetElem.getElem]
    have := GetAppend.eq.Get.fin X O (i := ⟨i, h_i⟩)
    simp at this
    rw [this]
    rfl
  ·
    aesop


@[path]
private lemma main
  {X : Tensor α (bz ++ n :: s)}
  {O : Tensor α (bz ++ m :: s)}
-- given
  (h : m = 0) :
-- imply
  X ++ O ≃ X := by
-- proof
  induction bz generalizing s with
  | nil =>
    have h := cons h X O
    have h := SEqDataS.of.SEq h
    rw [DataAppend.eq.Cast_AppendDataS] at h
    have h_eq : n * s.prod + m * s.prod = (n + m) * s.prod := by grind
    have h := SEq.of.SEqCast.Eq h (h := h_eq)
    apply SEq.of.SEqDataS.Eq (by simpa)
    rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
    simp
    apply SEqCast.of.SEq.Eq (by grind)
    symm
    apply SEq.trans h.symm
    apply SEq.of.All_EqGetS.Eq.fin (by grind)
    intro t
    have h_t := t.isLt
    have h_t : t < 1 * (n * s.prod + m * s.prod) := by
      simp [h_t]
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    fin_cases q
    simp at ⊢ h_qr
    have h_r := Fin.Eq_Fin.of.EqVal h_qr.symm
    simp [h_r]
    apply Get.of.Eq.Lt
    rw [Head.eq.Get_0.fin]
    rw [GetMap₂.eq.BFnGetS.fin]
    simp
    repeat erw [EqHeadSplitAt_0]
    rfl
  | cons b bz ih =>
    subst h
    apply SEq.of.All_SEqGetS.Eq.Eq
    ·
      simp
    ·
      intro i
      have h_i := i.isLt
      simp [GetElem.getElem]
      have := GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0.fin (by grind) X O (i := ⟨i, h_i⟩)
      simp at this
      rw [this]
      specialize ih (X := X.get i) (O := O.get i)
      assumption
    ·
      rfl


-- created on 2026-01-13
-- updated on 2026-05-03
