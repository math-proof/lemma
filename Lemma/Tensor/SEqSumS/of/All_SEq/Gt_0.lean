import Lemma.Finset.NeUnivEmpty.of.Gt_0
import Lemma.Tensor.SEqSumS.of.All_SEq.Ne_Empty
open Finset Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin m → Tensor α s'}
-- given
  (h_m : m > 0)
  (h : ∀ i : Fin m, X i ≃ Y i) :
-- imply
  ∑ i : Fin m, X i ≃ ∑ i : Fin m, Y i := by
-- proof
  apply SEqSumS.of.All_SEq.Ne_Empty
  ·
    apply NeUnivEmpty.of.Gt_0 h_m
  ·
    aesop


-- created on 2025-11-06
