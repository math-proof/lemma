import Lemma.Tensor.EqData0'0
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (h : s = s') :
-- imply
  (0 : Tensor α s) ≃ (0 : Tensor α s') := by
-- proof
  constructor
  ·
    assumption
  ·
    apply HEq.of.SEqDataS.Eq h
    repeat rw [EqData0'0]
    aesop


-- created on 2025-10-31
