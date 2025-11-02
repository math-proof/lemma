import sympy.tensor.tensor
import Lemma.Tensor.Data.eq.FlattenMapRange
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (s₀ :: s)) :
-- imply
  X.data = ((List.Vector.range s₀).map fun i => X.toVector[i].data).flatten := by
-- proof
  have := Data.eq.FlattenMapRange X
  simp [GetElem.getElem] at this
  simp [Tensor.get] at this
  rw [this]
  congr


-- created on 2025-05-18
