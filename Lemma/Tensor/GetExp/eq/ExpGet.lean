import sympy.tensor.functions
import Lemma.Tensor.LengthExp.eq.Length
import Lemma.Tensor.GetTensorMapData.eq.TensorMapDataGet
open Tensor


@[main, fin]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (exp X)[i]'(by simp [LengthExp.eq.Length]) = exp X[i] := by
-- proof
  apply GetTensorMapData.eq.TensorMapDataGet


-- created on 2025-10-08
