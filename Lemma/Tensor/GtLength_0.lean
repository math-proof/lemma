import sympy.tensor.Basic
import Lemma.Nat.Gt_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
open Tensor Nat


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (i : Fin X.length):
-- imply
  s.length > 0 := by
-- proof
  have h_length := Gt_0 i
  apply GtLength_0.of.GtLength_0 h_length


-- created on 2025-10-06
