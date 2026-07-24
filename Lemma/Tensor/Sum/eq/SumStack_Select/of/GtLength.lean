import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqGetCons
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GtGet.of.GtGetTail.GtLengthTail
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.Cast_SumStack.eq.SumStack_Cast.of.Eq
import Lemma.Tensor.EqGetStack.of.Lt
import Lemma.Tensor.Stack.of.All_Eq
import Lemma.Tensor.GetSelect.as.SelectGet.of.GtGet_0.GtGet_Add_1.LtAdd_1Length
import Lemma.Tensor.GetSumStack.eq.SumStack_Get.of.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqSumSStack.of.All_SEq.Eq.Eq
import Lemma.Tensor.SEqSumSStack.of.All_SEq.Eq.Gt_0
import Lemma.Tensor.Select_0.as.Get.of.GtLength_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.GtLength
import Lemma.Tensor.Sum.eq.Zero.of.Eq0Get.GtLength
import Lemma.Tensor.Sum.eq.Zero.of.EqGet_0'0.GtLength_0
import Lemma.Tensor.Sum_0.as.SumStack_Get.of.GtLength_0
open Bool List Nat Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (h : s.length > i)
  (X : Tensor α s) :
-- imply
  X.sum i = ∑ k < s[i], X.select ⟨i, h⟩ k := by
-- proof
  if h_i : s[i] = 0 then
    rw [Sum.eq.Zero.of.EqGet_0'0.GtLength_0 (by grind) h_i]
    rw [Sum.eq.Zero.of.Eq0Get.GtLength (by grind) (by grind)]
    rfl
  else
    induction i generalizing s X with
    | zero =>
      simp [Select_0.eq.Cast_Get.of.GtLength_0 h]
      rw [Sum_0.eq.Cast_SumStack_Get.of.GtLength_0.fin h]
      apply Cast_SumStack.eq.SumStack_Cast.of.Eq
      simp
    | succ i ih =>
      have h_i := Lt_Sub.of.LtAdd h
      have h_lt_length_tail : i < s.tail.length := by simpa
      rw [Sum.eq.Cast_Stack_Sum.of.GtLength (by grind)]
      apply EqCast.of.SEq
      rw [Stack.of.All_Eq.fin (f := fun t : Fin s[0] => (X[t]'(by apply GtLength.of.GtLength_0)).sum i) (g := fun t : Fin s[0] => ∑ k < s[i + 1], (X[t]'(by apply GtLength.of.GtLength_0)).select ⟨i, h_lt_length_tail⟩ ⟨k, by grind⟩)]
      ·
        apply SEq.of.All_SEqGetS.Eq.GtLength_0
        ·
          intro t
          have h_t := t.isLt
          simp
          have h_s := Gt_0.of.Gt h
          have h_t : t < s[0] := by
            simp only [GetElem.getElem] at h_t
            have := EqGetCons.fin (s.get ⟨0, by grind⟩) (s.tail.eraseIdx i)
            simp only [this] at h_t
            grind
          have := EqGetStack.of.Lt.fin h_t (fun j : Fin s[0] => ∑ k < s[i + 1], (X[j]'(GtLength.of.GtLength h X j)).select ⟨i, h_lt_length_tail⟩ ⟨k, by grind⟩)
          simp at this
          rw [this]
          erw [GetSumStack.eq.SumStack_Get.of.GtLength_0 _ (fun k : Fin s[i + 1] => X.select ⟨i + 1, h⟩ k) ⟨t, _⟩]
          ·
            simp only [GetElem.getElem]
            simp
            apply SEqSumSStack.of.All_SEq.Eq.Eq
            ·
              apply EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 h_i
            ·
              intro l
              apply SelectGet.as.GetSelect.of.GtGet_0.GtGet_Add_1.LtAdd_1Length h _ h_t
              ·
                simp
              ·
                apply GtGet.of.GtGetTail.GtLengthTail (by grind)
                grind
            ·
              simp
          ·
            rw [LengthEraseIdx.eq.SubLength_1.of.GtLength (by simpa)]
            apply Gt_0.of.Gt h_i
          ·
            rwa [GetEraseIdx.eq.Get.of.Gt.GtLength (by simpa) (by simp)]
        ·
          rw [EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0]
      ·
        intro j
        have h_j := GtLength.of.GtLength h X j
        rw [ih (by grind) X[j] (by grind)]
        apply Eq.of.SEq
        simp
        apply SEqSumSStack.of.All_SEq.Eq.Gt_0
        ·
          simp
          grind
        ·
          intro t
          rfl
        ·
          simp


-- created on 2026-07-22
-- updated on 2026-07-23
