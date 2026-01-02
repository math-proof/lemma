import Lemma.Tensor.Data.eq.FlattenMapRange_GetToVector
import Lemma.Tensor.DataGetToVector.as.ArraySliceData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqFlattenMapRange.of.All_SEqArraySlice
import sympy.tensor.tensor
open Tensor Vector


@[main]
private lemma main
  {a b : Tensor α (s₀ :: s)}
-- given
  (h : ∀ i : Fin s₀, a.toVector[i].data = b.toVector[i].data) :
-- imply
  a = b := by
-- proof
  apply Eq.of.EqDataS
  rw [Data.eq.FlattenMapRange_GetToVector b]
  let data : List.Vector α (s₀ * s.prod) := a.data
  have h_data : data = a.data := rfl
  rw [← h_data]
  apply Eq_FlattenMapRange.of.All_SEqArraySlice
  rw [h_data]
  intro i
  have h_eq := ArraySliceData.as.DataGetToVector a i
  apply h_eq.trans
  rw [h i]


-- created on 2025-05-18
-- updated on 2025-11-11
