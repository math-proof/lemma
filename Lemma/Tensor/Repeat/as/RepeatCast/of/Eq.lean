import sympy.tensor.Basic
import stdlib.SEq
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import Lemma.List.Set.ne.Nil.of.Ne_Nil
import Lemma.List.Ne_Nil
import Lemma.Nat.LtVal
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
open Tensor List Nat


@[main, comm 1]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  X.repeat n d ≃ ((cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simp [← h]⟩) := by
-- proof
  apply SEq.of.All_SEqGetS.Eq.Ne_Nil
  ·
    apply Set.ne.Nil.of.Ne_Nil
    have := Ne_Nil d
    aesop
  ·
    intro i
    have h_i := LtVal i
    by_cases h_d : d.val > 0
    ·
      simp [LengthRepeat.eq.Get_0.of.GtVal_0 h_d] at h_i
      have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0.fin h_d h_i X (d := d) n
      apply SEq.trans this
      simp [h] at h_i
      have := GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0.fin (by simpa) h_i (cast (congrArg (Tensor α) h) X) (d := ⟨d, by simp [← h]⟩) n
      apply SEq.symm ∘ SEq.trans this
      ·
        simp
        have h_s := Gt_0 d
        rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin h_s h X ⟨i, by simpa⟩]
        simp
        sorry
      ·
        simp [h]
    ·
      simp at h_d
      sorry


-- created on 2025-10-10
