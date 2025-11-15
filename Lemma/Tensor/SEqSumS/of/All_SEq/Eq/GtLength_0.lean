import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.SEqSumS.of.All_SEq.Gt_0
import Lemma.Tensor.Sum_0.eq.Cast_Sum_Get.of.GtLength_0
open Bool Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h_length : s.length > 0)
  (h_s : s = s')
  (h : ∀ i : Fin s[0], X.get ⟨i, by apply Lt_Length.of.GtLength_0 h_length⟩ ≃ Y.get ⟨i, by apply Lt_Length.of.GtLength_0 (h_s ▸ h_length) Y ⟨i, by grind⟩⟩) :
-- imply
  X.sum 0 ≃ Y.sum 0 := by
-- proof
  have h_length' := h_s ▸ h_length
  repeat rw [Sum_0.eq.Cast_Sum_Get.of.GtLength_0.fin (by assumption)]
  apply SEqCastS.of.SEq.Eq.Eq
  repeat simp
  if h₀ : s[0] = 0 then
    match s with
    | [] =>
      contradiction
    | s₀ :: s =>
      aesop
  else
    have := SEqSumS.of.All_SEq.Gt_0 (by omega) h
    aesop


-- created on 2025-11-06
