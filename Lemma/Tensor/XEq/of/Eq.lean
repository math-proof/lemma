import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEq.of.Eq
open Tensor


@[main]
private lemma main
  [XEq α]
  {A B : Tensor α s}
-- given
  (h : A = B) :
-- imply
  A ≈ B := by
-- proof
  apply XEq.of.XEqDataS
  exact Vector.XEq.of.Eq (EqDataS.of.Eq h)


-- created on 2026-07-29
