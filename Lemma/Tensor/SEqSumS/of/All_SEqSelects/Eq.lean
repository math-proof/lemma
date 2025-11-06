import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.Lt_Length.of.GtLength
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
  sorry


-- created on 2025-11-06
