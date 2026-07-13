import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1.Ge_0
import Lemma.Tensor.GetPermute.as.PermuteGet.of.GtGet_0.GtLength.Gt_0.Ge_0
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SEqPermuteS.of.SEq.GtLength
import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
import Lemma.List.TailPermute__Neg.eq.PermuteTail.of.Ge
import Lemma.Tensor.GetPermute__Neg.as.Permute__Neg_Get.of.Gt.GtGet_0.GtLength
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermuteS.of.Eq.EqValS.Eq
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.Swap.eq.PermutePermute.of.Lt.GtLength
import Lemma.Tensor.GetDite.eq.Get.of.Not
import Lemma.Tensor.LengthTranspose.eq.Length.of.GtLength_2
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
open Bool List Tensor


@[main, fin]
private lemma main
-- given
  (X : Tensor α ((b :: bz) ++ [m, n]))
  (i : Fin b) :
-- imply
  have : i < Xᵀ.length := by
    rw [LengthTranspose.eq.Length.of.GtLength_2]
    repeat grind
  Xᵀ[i] ≃ X[i]ᵀ := by
-- proof
  simp [GetElem.getElem]
  unfold Tensor.T
  simp
  unfold Tensor.transpose
  simp
  apply SEq_Cast.of.SEq.Eq
  ·
    simp
    rw [Swap.eq.PermutePermute.of.Lt.GtLength]
    ·
      simp
      repeat rw [EqPermuteS.of.Eq.EqValS.Eq]
      ·
        rfl
      ·
        simp
      ·
        simp
      ·
        rfl
      ·
        rfl
    ·
      grind
    ·
      grind
  ·
    split_ifs with h
    ·
      omega
    ·
      repeat rw [GetDite.eq.Get.of.Not.fin (by grind)]
      let bz' := bz ++ [m, n]
      have h_bz : bz.length + 1 < (b :: bz').length := by
        grind
      have h_bz := GetPermute.eq.Get.of.Gt (i := ⟨bz.length + 1, h_bz⟩) (j := 0) (s := b :: bz') (d := 0) (by grind)
      simp at h_bz
      let bz'1 := bz'.length + 1 - 2
      let args := (bz'.length, bz'1)
      let args' := (bz'1, bz'.length)
      have h_i : i < (((b :: bz').permute ⟨(if bz'1 > bz'.length then
        args
      else
        args').1, by grind⟩
        (↑((if bz'1 > bz'.length then
          args
        else
          args').2 - (if bz'1 > bz'.length then
          args
        else
          args').1) - 1)).permute
          ⟨(if bz'1 > bz'.length then
            args
          else
            args').2, by simp [bz', args, args', bz'1]⟩
          (-↑((if bz'1 > bz'.length then
            args
          else
            args').2 - (if bz'1 > bz'.length then
            args
          else
            args').1)))[0]'(by simp) := by
        simp only [GetElem.getElem]
        rw [GetPermute__Neg.eq.Get_0.of.Gt.fin (by simp [bz', args, args', bz'1])]
        simp [h_bz, bz', args, args', bz'1]
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, h_i⟩)]
      ·
        simp
        apply SEqCast.of.SEq.Eq
        ·
          simp
          apply congrArg
          rw [Swap.eq.PermutePermute.of.Lt.GtLength]
          ·
            simp [bz', args, args', bz'1]
            repeat rw [EqPermuteS.of.Eq.EqValS.Eq]
            repeat simp
          ·
            simp
          ·
            simp
        ·
          rw [GetPermute__Neg.eq.Cast_Permute__Neg_Get.of.Gt.GtGet_0.GtLength]
          .
            apply SEqCast.of.SEq.Eq
            .
              simp [bz', args, args', bz'1]
              let s := ((b :: bz').permute ⟨(if bz'1 > bz'.length then
                args
              else args').1, by grind⟩ (↑((if bz'1 > bz'.length then
                args
              else args').2 - (if bz'1 > bz'.length then args
              else args').1) - 1))
              have := PermuteTail.eq.TailPermute__Neg.of.Ge (i := ⟨bz.length + 1, by grind⟩) (d := 1) (by grind) (s := s)
              simp [s, bz', args, args', bz'1] at this
              rw [this]
            .
              apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
              .
                simp
              .
                simp
              .
                erw [GetPermute.eq.Cast_PermuteGet.of.GtGet_0.GtLength.Gt_0.Ge_0]
                .
                  apply SEqCast.of.SEq.Eq
                  .
                    rw [PermuteTail.eq.TailPermute.of.GtLength_Add_1.Ge_0]
                    repeat simp
                  .
                    apply Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
                    .
                      simp
                    .
                      simp
                    .
                      rfl
                .
                  grind
                .
                  grind
                .
                  grind
          .
            simp [h_bz, bz']
          .
            simp
      ·
        simp
        rw [Swap.eq.PermutePermute.of.Lt.GtLength]
        ·
          simp [bz', args, args', bz'1]
          repeat rw [EqPermuteS.of.Eq.EqValS.Eq]
          repeat simp
        ·
          simp
        ·
          simp


-- created on 2026-07-03
-- updated on 2026-07-04
