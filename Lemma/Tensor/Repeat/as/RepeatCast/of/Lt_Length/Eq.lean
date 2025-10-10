import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.List.Set.ne.Nil.of.Ne_Nil
import Lemma.List.Ne_Nil.of.GtLength
import Lemma.Bool.SEqCast.of.Eq.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Nat.LtVal
open Tensor List Bool Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (h_d : d < s.length)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat n ⟨d, h_d⟩ ≃ (cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simpa [← h]⟩ := by
-- proof
  induction d generalizing s s' X with
  | zero =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    .
      apply Set.ne.Nil.of.Ne_Nil
      aesop
    .
      intro i
      have h_i := LtVal i
      simp [LengthRepeat.eq.Mul_Get_0.of.GtLength_0 h_d] at h_i
      have := GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0.fin h_d h_i X
      apply SEq.trans this
      have := GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0.fin (by simpa [← h]) (by simpa [← h]) (cast (congrArg (Tensor α) h) X)
      apply SEq.symm ∘ SEq.trans this
      have h_s' : s'.length > 0 := by
        simpa [← h]
      have h_s₀ := Gt_0.of.GtMul h_i
      rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin h_d h X ⟨i % s'[0], by simp_all [LtMod.of.Gt_0 (by simpa [← h]) i (d := s'[0])]⟩]
      apply SEqCast.of.Eq.Eq
      repeat simp [h]
  | succ d ih =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    .
      apply Set.ne.Nil.of.Ne_Nil
      apply Ne_Nil.of.GtLength h_d
    .
      intro i
      have h_i := LtVal i
      have h_s := Gt_0.of.Gt h_d
      have h_pos : (⟨d + 1, by assumption⟩ : Fin s.length).val > 0 := by simp
      simp [LengthRepeat.eq.Get_0.of.GtVal_0 (by simp) (d := ⟨d + 1, by assumption⟩)] at h_i
      have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0.fin h_pos h_i X (d := ⟨d + 1, by assumption⟩) n
      apply SEq.trans this
      simp [h] at h_i
      have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0.fin (by simp) h_i (cast (congrArg (Tensor α) h) X) (d := ⟨d + 1, by simpa [← h]⟩) n
      apply SEq.of.SEq.SEq _ this
      .
        rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin h_s h X ⟨i, by simpa⟩]
        have h := congrArg (List.tail) h
        apply ih h (by simp; omega) (X.get ⟨i, by simpa [Length.eq.Get_0.of.GtLength h_d X]⟩)
      .
        simp [h]


-- created on 2025-10-10
