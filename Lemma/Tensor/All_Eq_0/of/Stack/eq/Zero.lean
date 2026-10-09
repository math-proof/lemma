import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGet0_0
open Tensor


@[path]
private lemma main
  [Zero α]
  {f : Fin n → Tensor α s}
-- given
  (h : [i < n] f i = 0) :
-- imply
  ∀ i : Fin n, f i = 0 := by
-- proof
  intro i
  rw [← EqGetStack f i, h]
  apply EqGet0_0.fin


-- created on 2022-01-01
