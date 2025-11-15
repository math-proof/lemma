import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Gt_0
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin n → Tensor α s'}
-- given
  (h_s : s = s')
  (h_n : m = n)
  (h : ∀ i : Fin m, X i ≃ Y ⟨i, by grind⟩) :
-- imply
  ∑ i : Fin m, X i ≃ ∑ i : Fin n, Y i := by
-- proof
  if h_m : m = 0 then
    subst h_m h_n
    aesop
  else
    apply SEqSumS.of.All_SEq.Eq.Gt_0 _ h_n h
    omega


-- created on 2025-11-15
