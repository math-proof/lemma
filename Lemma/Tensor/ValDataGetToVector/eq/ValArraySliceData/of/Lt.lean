import sympy.tensor.tensor
import Lemma.Tensor.ValDataGetToVector.eq.ValArraySliceData
open Tensor


@[main]
private lemma main
-- given
  (h : i < s₀)
  (X : Tensor α (s₀ :: s)) :
-- imply
  X.toVector[i].data.val = (X.data.array_slice (i * s.prod) s.prod).val := by
-- proof
  erw [ValDataGetToVector.eq.ValArraySliceData X ⟨i, h⟩]


-- created on 2025-06-29
