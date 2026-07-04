import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
open Tensor


@[main]
private lemma main
  {i : Fin s.length}
-- given
  (h : i.val > 0)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.permute i d).length = X.length := by
-- proof
  rw [LengthPermute.eq.Get_0.of.GtVal_0 h]
  rw [Length.eq.Get_0.of.GtLength_0]


-- created on 2026-07-04
