import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.GetSumStack.eq.SumStack_Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
open List Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (h : s = s')
  (X : Fin n → Tensor α s) :
-- imply
  ∑ i < n, X i ≃ ∑ i < n, cast (congrArg (Tensor α) h) (X i) := by
-- proof
  if h_s : s = [] then
    subst h_s
    aesop
  else
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil h_s h
    intro i
    have h_s := GtLength_0.of.Ne_Nil h_s
    have h_i : i < s[0] := by simp [← Length.eq.Get_0.of.GtLength_0 h_s (∑ i < n, X i)]
    have := GetSumStack.eq.SumStack_Get.of.GtLength_0 h_s X ⟨i, h_i⟩
    simp at this
    rw [this]
    let X' : Fin n → Tensor α s' := fun j => cast (congrArg (Tensor α) h) (X j)
    aesop


-- created on 2026-07-22
