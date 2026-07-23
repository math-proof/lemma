import Lemma.Tensor.SEqSumSStack.of.All_SEq.Gt_0
open Tensor


@[main]
private lemma main
  [AddMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin n → Tensor α s'}
-- given
  (h_m : m > 0)
  (h_n : m = n)
  (h : ∀ i : Fin m, X i ≃ Y ⟨i, by grind⟩) :
-- imply
  ∑ i < m, X i ≃ ∑ i < n, Y i := by
-- proof
  subst h_n
  simp at h
  apply SEqSumSStack.of.All_SEq.Gt_0 h_m h


-- created on 2026-07-22
-- updated on 2026-07-23
