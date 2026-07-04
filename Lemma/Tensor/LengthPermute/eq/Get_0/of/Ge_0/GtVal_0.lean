import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Length.of.Ge_0.GtVal_0
open Tensor


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h_i : i.val > 0)
  (h_d : d ≥ 0)
  (X : Tensor α s) :
-- imply
  (X.permute i d).length = s[0] := by
-- proof
  rw [LengthPermute.eq.Length.of.Ge_0.GtVal_0 h_i]
  apply Length.eq.Get_0.of.GtLength_0
  assumption


-- created on 2026-07-04
