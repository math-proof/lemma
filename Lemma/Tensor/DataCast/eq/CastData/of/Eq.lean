import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  have h_X : Tensor α s = Tensor α s' := by rw [h]
  (cast h_X X).data = cast (by rw [h]) X.data := by
-- proof
  aesop


-- created on 2025-09-21
