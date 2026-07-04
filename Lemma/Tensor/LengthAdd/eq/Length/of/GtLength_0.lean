import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Add α]
-- given
  (h : s.length > 0)
  (X Y : Tensor α s) :
-- imply
  (X + Y).length = X.length := by
-- proof
  repeat rw [Length.eq.Get_0.of.GtLength_0 h]


-- created on 2026-07-04
