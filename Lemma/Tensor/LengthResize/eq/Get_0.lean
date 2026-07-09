import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthResize.eq.Length
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  have h_i := i.isLt
  (X.resize i s[0]).length = s[0] := by
-- proof
  intro h_i
  rw [LengthResize.eq.Length X i]
  rw [Length.eq.Get_0.of.GtLength_0]


-- created on 2026-07-09
