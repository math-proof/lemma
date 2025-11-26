import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Nat.LtVal
import Lemma.Nat.LtSubS.of.Lt.Le
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.GetSet.eq.Get.of.Gt.GtLength
import Lemma.Nat.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Tensor.GetToVector.eq.Get.of.GtLength_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Bool.SEqCast.of.Eq.Eq
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Vector.EqGetRange
open Tensor List Vector Bool Nat


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  let s₀ := (s.set d (n * s[d])).headD 1
  have h_s := Gt_0 d
  have h_s₀ : s₀ = s.headD 1 := by
    simp only [s₀]
    repeat rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
    apply GetSet.eq.Get.of.Gt.GtLength h_s h
  have h_head := HeadD.eq.Get_0.of.GtLength_0 h_s 1
  have h_d_1 : d - 1 < s.tail.length := by
    simp
    apply LtSubS.of.Lt.Le (by linarith) (by simp)
  (X.repeat n d).toVector = (List.Vector.range s₀).map fun i =>
    have := LtVal i
    have : i < (X.repeat n d).length := by simp_all [LengthRepeat.eq.Get_0.of.GtVal_0 h]
    cast
      (by
        congr
        simp
        congr
        repeat apply EqAddSub.of.Ge (by linarith)
      )
      ((X.get ⟨i, GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩⟩).repeat n ⟨d - 1, h_d_1⟩) := by
-- proof
  intro s₀ h_s h_s₀ h_head h_d_1
  ext i
  simp
  rw [GetToVector.eq.Get.of.GtLength_0.headD (by simpa)]
  apply Eq_Cast.of.SEq
  simp
  have hi := i.isLt
  simp only [HeadD.eq.Get_0.of.GtLength_0 (by simp_all) (s := s.set d (n * s[d]))] at hi
  rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by assumption) (by assumption)] at hi
  have h_eq := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0 h hi X n
  simp at h_eq
  simp only [GetElem.getElem] at h_eq
  rw [h_eq]
  apply SEqCast.of.Eq.Eq
  ·
    rw [TailSet.eq.SetTail.of.Gt_0 (by assumption)]
    rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1]
    ·
      have h_d := Ge_1.of.Gt_0 h
      simp [EqAddSub.of.Ge h_d]
    ·
      simp at h_d_1
      assumption
  ·
    congr
    simp [s₀]
    rw [EqGetRange.fin]


-- created on 2025-10-05
-- updated on 2025-10-06
