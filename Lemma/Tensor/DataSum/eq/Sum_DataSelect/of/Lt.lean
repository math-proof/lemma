import Lemma.Tensor.DataSum.eq.Sum_Data
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
open Tensor


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α s)
  (h_d : d < s.length) :
-- imply
  (X.sum d).data = ∑ i, (X.select ⟨d, h_d⟩ i).data := by
-- proof
  have := DataSum.eq.Sum_DataSelect X ⟨d, h_d⟩
  aesop


-- created on 2026-04-24
