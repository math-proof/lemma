import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Tensor.Sum.eq.Sum_Select
open Tensor


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  (X.sum d).data = ∑ i, (X.select d i).data := by
-- proof
  rw [Sum.eq.Sum_Select]
  rw [DataSum.eq.Sum_Data]


-- created on 2025-11-28
