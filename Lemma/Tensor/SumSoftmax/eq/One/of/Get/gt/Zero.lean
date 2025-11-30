import Lemma.Tensor.SEqSumS.of.SEq.Eq
import Lemma.Bool.Eq.of.SEq.SEq
import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.Ge
import Lemma.List.GetPermute.eq.Get.of.Ge
import Lemma.Nat.EqSub_Sub.of.Ge
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.Gt_0
import Lemma.Nat.Le_Sub_1
import Lemma.Tensor.SEq1S.of.Eq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.Softmax.as.PermuteSoftmaxPermute.of.LtAdd_1Length
import Lemma.Tensor.SumPermute.as.PermuteSum.of.Ge
import Lemma.Tensor.SumSoftmax.eq.One.of.Get_SubLength_1.gt.Zero.GtLength_0
open Bool List Nat Tensor


/--
自然语言论述：[flash_attn](http://myhz0606.com/article/flash_attn)
-/
@[main]
private lemma main
  [ExpPos α] [IsOrderedCancelAddMonoid α]
  {i : Fin s.length}
-- given
  (h : s[i] > 0)
  (X : Tensor α s) :
-- imply
  (X.softmax i).sum i = 1 := by
-- proof
  if h_i : i = s.length - 1 then
    have h_pos := Gt_0 i
    have h_i : i = ⟨s.length - 1, by simp [h_pos]⟩ := Eq_Mk.of.EqVal h_i
    subst h_i
    simp
    apply SumSoftmax.eq.One.of.Get_SubLength_1.gt.Zero.GtLength_0 h_pos h
  else
    have := Softmax.as.PermuteSoftmaxPermute.of.LtAdd_1Length (i := i) (by omega) X
    have := SEqSumS.of.SEq this i
    apply Eq.of.SEq.SEq this
    simp
    have := SumPermute.as.PermuteSum.of.Ge (i := ⟨s.length - 1, by simp; grind⟩) (d := s.length - 1 - i) (by simp) ((X.permute i ↑(s.length - 1 - i)).softmax (s.length - 1))
    simp at this
    rw [EqSub_Sub.of.Ge (by omega)] at this
    apply SEq.trans this
    have h_sum : ((X.permute i ↑(s.length - 1 - i)).softmax (s.length - 1)).sum (s.length - 1) ≃ ((X.permute i ↑(s.length - 1 - i)).softmax (s.length - 1)).sum := SEqSumS.of.SEq.Eq (by simp) (by rfl)
    apply SEq.trans h_sum
    have := GetPermute.eq.Get.of.Ge (s := s) (i := i) (j := ⟨s.length - 1, by grind⟩) (Le_Sub_1 i)
    simp at this
    have := SumSoftmax.eq.One.of.Get_SubLength_1.gt.Zero.GtLength_0 (by simp; omega) (by simpa [this]) (X.permute i ↑(s.length - 1 - ↑i))
    simp at this
    rw [this]
    apply SEq1S.of.Eq
    simp
    apply EraseIdxPermute.eq.EraseIdx.of.Ge (j := ⟨s.length - 1, by grind⟩)
    apply Le_Sub_1


-- created on 2025-10-03
-- updated on 2025-10-31
