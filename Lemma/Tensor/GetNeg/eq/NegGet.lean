import sympy.tensor.functions
import Lemma.Tensor.LengthNeg.eq.Length
import Lemma.Tensor.GetTensorMapData.eq.TensorMapDataGet
import sympy.Basic'
open Tensor


@[main, fin]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (-X)[i]'(by simp [LengthNeg.eq.Length]) = -X[i] := by
-- proof
  apply GetTensorMapData.eq.TensorMapDataGet


-- created on 2025-10-08
