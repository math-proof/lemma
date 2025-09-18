import Lemma.Algebra.SubAdd.eq.AddSub.of.Le
import Lemma.Logic.IffEqS.of.Eq
import Lemma.Algebra.GetAppend.eq.Get.of.Lt_Length
import Lemma.Algebra.Lt_Sub.of.LtAdd
import Lemma.Algebra.GetDrop.eq.Get_Add.of.Add.lt.Length
import Lemma.Algebra.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.Algebra.Add
import Lemma.Algebra.SubAdd.eq.Sub_Sub.of.Ge
import Lemma.Algebra.GetElem!.eq.None.of.Ge_Length
import Lemma.Algebra.LeSub.is.Le_Add
open Algebra Logic


@[main]
private lemma main
-- given
  (h : i ≤ a.length)
  (b : List α) :
-- imply
  (a ++ b).drop i = a.drop i ++ b := by
-- proof
  ext j x
  by_cases h_ij : i + j < a.length + b.length
  ·
    have h_j : j < ((a ++ b).drop i).length := by
      simp_all
      apply Lt_Sub.of.LtAdd.left.nat h_ij
    simp at h_j
    rw [SubAdd.eq.AddSub.of.Le (by assumption)] at h_j
    simp_all
    apply IffEqS.of.Eq
    by_cases h_j : i + j < a.length
    ·
      have h_j := Lt_Sub.of.LtAdd.left.nat h_j
      repeat rw [GetAppend.eq.Get.of.Lt_Length (by simp_all)]
      rw [GetDrop.eq.Get_Add.of.Add.lt.Length (by simp_all)]
    ·
      simp at h_j
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
      rw [Add.comm] at h_j
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
      simp_all [Sub_Sub.eq.SubAdd.of.Ge]
      simp [Add.comm]
  ·
    simp at h_ij
    rw [GetElem!.eq.None.of.Ge_Length]
    ·
      rw [GetElem!.eq.None.of.Ge_Length]
      simp
      rw [AddSub.eq.SubAdd.of.Le (by assumption)]
      apply LeSub.of.Le_Add.left.nat h_ij
    ·
      simp_all [Add.comm]


-- created on 2025-06-20
