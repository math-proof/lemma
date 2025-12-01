import sympy.tensor.functions
import Lemma.Tensor.LengthNeg.eq.Length
import Lemma.Tensor.GetTensorMapData.eq.TensorMapDataGet
open Tensor


@[main]
private lemma fin
  [Neg α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (-X).get ⟨i, by simp [LengthNeg.eq.Length]⟩ = -(X.get i) := by
-- proof
  apply GetTensorMapData.eq.TensorMapDataGet


@[main]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have hi : i < (-X).length := by simp [LengthNeg.eq.Length]
  (-X)[i] = -X[i] := by
-- proof
  apply fin


-- created on 2025-10-08
