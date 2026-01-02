import sympy.tensor.functions
import Lemma.Tensor.LengthInv.eq.Length
import Lemma.Tensor.GetTensorMapData.eq.TensorMapDataGet
open Tensor


@[main, fin]
private lemma main
  [Inv α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X⁻¹[i]'(by simp [LengthInv.eq.Length]) = X[i]⁻¹ := by
-- proof
  apply GetTensorMapData.eq.TensorMapDataGet


-- created on 2025-10-08
