import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Data.eq.FlattenMapRange_GetToVector
import Lemma.Vector.Eq_FlattenMapRange.of.All_EqValS
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Tensor.DataGetToVector.as.ArraySliceData
import Lemma.Vector.EqValS.of.Eq
open Tensor Logic Vector


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
  apply Eq_FlattenMapRange.of.All_EqValS
  rw [h_data]
  intro i
  have h_eq := DataGetToVector.as.ArraySliceData a i
  rw [← EqValS.of.Eq h_eq]
  have hi := h i
  apply EqUFnS.of.Eq hi (·.val)


-- created on 2025-05-18
-- updated on 2025-05-23
