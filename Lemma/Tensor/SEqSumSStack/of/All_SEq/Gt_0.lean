import Lemma.Tensor.SEqSumSStack.of.All_SEq.Eq
open Tensor


@[main]
private lemma main
  [AddMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin m → Tensor α s'}
-- given
  (h_m : m > 0)
  (h : ∀ i : Fin m, X i ≃ Y i) :
-- imply
  ∑ i < m, X i ≃ ∑ i < m, Y i := by
-- proof
  have h₀ := h ⟨0, by grind⟩
  have h_s := h₀.left
  apply SEqSumSStack.of.All_SEq.Eq h_s h


-- created on 2026-07-22
-- updated on 2026-07-23
