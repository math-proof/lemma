import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.List.Lt_Get.of.Lt_GetTail.Lt_LengthTail
import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EqGetCons
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.LtVal
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.Cast_Sum.eq.Sum_Cast.of.Eq
import Lemma.Tensor.EqGetStack.of.Lt
import Lemma.Tensor.EqStackS.of.All_Eq
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Lt_Length.of.GtLength
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Tensor.Sum.eq.Cast_Stack_Sum.of.LtAdd_1Length
import Lemma.Tensor.Sum_0.eq.Cast_Sum_Get.of.GtLength_0
import sympy.tensor.tensor
open Bool List Nat Tensor


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > i)
  (X : Tensor α s) :
-- imply
  X.sum i = ∑ k : Fin s[i], X.select ⟨i, h⟩ k := by
-- proof
  induction i generalizing s X with
  | zero =>
    simp [Select_0.eq.Cast_Get.of.GtLength_0 h]
    rw [Sum_0.eq.Cast_Sum_Get.of.GtLength_0.fin h]
    apply Cast_Sum.eq.Sum_Cast.of.Eq
    simp
  | succ i ih =>
    have h_i := Lt_Sub.of.LtAdd h
    have h_lt_length_tail : i < s.tail.length := by simpa
    rw [Sum.eq.Cast_Stack_Sum.of.LtAdd_1Length h]
    apply EqCast.of.SEq
    rw [EqStackS.of.All_Eq.fin]
    .
      apply SEq.of.All_SEqGetS.Eq.GtLength_0
      ·
        intro t
        have h_t := LtVal t
        simp
        have h_s := Gt_0.of.Gt h
        simp only [EqGetCons] at h_t
        have := EqGetStack.of.Lt.fin h_t (fun j : Fin s[0] => ∑ k, (X[j]'(Lt_Length.of.GtLength h X j)).select ⟨i, h_lt_length_tail⟩ k)
        simp at this
        rw [this]
        rw [GetSum.eq.Sum_Get.of.GtLength_0.fin _ (fun k : Fin s[i + 1] => X.select ⟨i + 1, h⟩ k) ⟨t, _⟩]
        ·
          simp only [GetElem.getElem]
          simp
          apply Tensor.SEqSumS.of.All_SEq.Eq.Eq
          .
            apply EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 h_i
          .
            intro l
            apply Tensor.SelectGet.as.GetSelect.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length h _ h_t
            .
              simp
            .
              apply List.Lt_Get.of.Lt_GetTail.Lt_LengthTail
              simp
              grind
          .
            simp
        ·
          rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by simpa)]
          apply Gt_0.of.Gt h_i
        ·
          rwa [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by simpa) (by simp)]
      .
        rw [EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0]
    .
      intro j
      apply ih


-- created on 2025-11-07
