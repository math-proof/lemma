import Lemma.Tensor.HEq.of.HEqDataS.Eq
import Lemma.Logic.HEq.of.SEq
open Tensor Logic


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s')
  (h : A.data ≃ B.data) :
-- imply
  HEq A B := by
-- proof
  apply HEq.of.HEqDataS.Eq h_s
  apply HEq.of.SEq h


-- created on 2025-07-24
