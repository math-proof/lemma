import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Tensor α s}
  {Y : Tensor α s'}
  {i : Fin s.length}
-- given
  (h_s : s = s')
  (h : ∀ k : Fin s[i], X.select i k ≃ Y.select ⟨i, by simp [← h_s]⟩ ⟨k, by simp [← h_s]⟩) :
-- imply
  X.sum i ≃ Y.sum i := by
-- proof
  rw [Sum.eq.Sum_Select]
  rw [Sum.eq.Sum_Select.of.GtLength]
  apply SEqSumS.of.All_SEq.Eq.Eq _ _ h
  repeat aesop


-- created on 2025-11-06
-- updated on 2025-11-15
