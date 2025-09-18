import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.HEq.of.SEqDataS.Eq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s')
  (h : A.data ≃ B.data) :
-- imply
  A ≃ B := by
-- proof
  constructor
  .
    assumption
  .
    apply HEq.of.SEqDataS.Eq
    repeat assumption


-- created on 2025-06-29
