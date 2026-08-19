import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
-- given
  (v : List.Vector (Tensor α s) n) :
-- imply
  (Tensor.OfVector v).data = (v.map Tensor.data).flatten := by
-- proof
  unfold Tensor.OfVector
  simp


-- created on 2025-11-01
