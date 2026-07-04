import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthRepeat.eq.Length.of.GtVal_0
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n d).length = s[0] := by
-- proof
  rw [LengthRepeat.eq.Length.of.GtVal_0 h]
  rw [Length.eq.Get_0.of.GtLength_0]


-- created on 2025-07-05
-- updated on 2026-07-04
