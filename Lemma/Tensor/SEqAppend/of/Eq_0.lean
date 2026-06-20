import Lemma.Vector.EqHeadSplitAt_0
import Lemma.Vector.GetMap₂.eq.BFnGetS
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.EqGetS.of.Eq.Lt
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Fin.Eq_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Tensor.DataAppend.eq.Cast_Append
import Lemma.Tensor.DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.GetAppend.as.AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetAppend.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin Tensor Vector


@[main]
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
  ·
    aesop


@[main]
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
    rw [DataAppend.eq.Cast_Append] at h
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
    simp [Fin.Eq_0 q] at  ⊢ h_qr
    have h_r := Fin.Eq_Fin.of.EqVal h_qr.symm
    simp [h_r]
    apply EqGetS.of.Eq.Lt
    rw [Head.eq.Get_0.fin]
    rw [GetMap₂.eq.BFnGetS.fin]
    simp
    repeat rw [EqHeadSplitAt_0]
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
