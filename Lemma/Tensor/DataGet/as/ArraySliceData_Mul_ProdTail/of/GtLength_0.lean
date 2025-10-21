import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.DataGetToVector.as.ArraySliceData
import Lemma.Tensor.SEqArraySliceSData.of.Eq
import Lemma.Tensor.ValDataGetToVector.eq.ValArraySliceData
import Lemma.Tensor.ValDataGetToVector.eq.ValArraySliceData.of.Lt_Get_0.GtLength_0
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Vector.HEq.of.EqValS
import Lemma.Nat.LtVal
open Tensor List Vector Nat


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have : i < X.length := by simp [Length.eq.Get_0.of.GtLength_0 h]
  X[i].data ≃ X.data.array_slice (i * s.tail.prod) s.tail.prod := by
-- proof
  intro h_length
  simp only [GetElem.getElem]
  simp [Tensor.get]
  simp [SEq]
  constructor
  .
    rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
    simp [Le_SubMulS.of.Lt]
  .
    apply HEq.of.EqValS
    rw [ValDataGetToVector.eq.ValArraySliceData.of.Lt_Get_0.GtLength_0 (by assumption)]
    apply LtVal i


-- created on 2025-06-29
