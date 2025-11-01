import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
-- given
  (v : List.Vector (Tensor α s) n) :
-- imply
  (Tensor.fromVector v).data = (v.map Tensor.data).flatten := by
-- proof
  unfold Tensor.fromVector
  simp


-- created on 2025-11-01
