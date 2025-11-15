import Lemma.Tensor.SEqSumS.of.All_SEq.Gt_0
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin n → Tensor α s'}
-- given
  (h_m : m > 0)
  (h_n : m = n)
  (h : ∀ i : Fin m, X i ≃ Y ⟨i, by grind⟩) :
-- imply
  ∑ i : Fin m, X i ≃ ∑ i : Fin n, Y i := by
-- proof
  subst h_n
  simp at h
  apply SEqSumS.of.All_SEq.Gt_0 h_m h


-- created on 2025-11-15
