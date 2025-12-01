import sympy.tensor.functions
import Lemma.Tensor.LengthInv.eq.Length
import Lemma.Tensor.GetTensorMapData.eq.TensorMapDataGet
open Tensor


@[main]
private lemma fin
  [Inv α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (X⁻¹).get ⟨i, by simp [LengthInv.eq.Length]⟩ = (X.get i)⁻¹ := by
-- proof
  apply GetTensorMapData.eq.TensorMapDataGet


@[main]
private lemma main
  [Inv α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have hi : i < X⁻¹.length := by simp [LengthInv.eq.Length]
  X⁻¹[i] = X[i]⁻¹ := by
-- proof
  apply fin


-- created on 2025-10-08
