import Lemma.Tensor.HEq.of.SEqDataS.Eq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (h : n = n') :
-- imply
  (0 : List.Vector α n) ≃ (0 : List.Vector α n') := by
-- proof
  aesop


-- created on 2025-11-05
