import Lemma.Tensor.SEqSumSStack.of.All_SEq.Eq.Gt_0
open Tensor


@[main]
private lemma main
  [AddMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin n → Tensor α s'}
-- given
  (h_s : s = s')
  (h_n : m = n)
  (h : ∀ i : Fin m, X i ≃ Y ⟨i, by grind⟩) :
-- imply
  ∑ i < m, X i ≃ ∑ i < n, Y i := by
-- proof
  if h_m : m = 0 then
    subst h_m h_n
    aesop
  else
    apply SEqSumSStack.of.All_SEq.Eq.Gt_0 _ h_n h
    omega


-- created on 2026-07-23
