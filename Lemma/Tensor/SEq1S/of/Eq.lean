import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.Ge
import Lemma.Nat.Le_Sub_1
import Lemma.Tensor.EqData1'1
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import sympy.tensor.tensor
open List Nat Tensor


@[main]
private lemma main
  [One α]
-- given
  (h : s = s') :
-- imply
  (1 : Tensor α s) ≃ (1 : Tensor α s') := by
-- proof
  constructor
  ·
    assumption
  ·
    apply HEq.of.SEqDataS.Eq h
    repeat rw [EqData1'1]
    aesop


-- created on 2025-10-31
