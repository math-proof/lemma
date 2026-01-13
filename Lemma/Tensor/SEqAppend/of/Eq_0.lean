import Lemma.Tensor.GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetAppend.eq.Get
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
open Tensor


@[main]
private lemma cons
  {X : Tensor α (n :: s)}
  {O : Tensor α (m :: s)}
-- given
  (h : m = 0) :
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
    apply cons h
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
