import sympy.tensor.Basic
import sympy.Basic


@[main, comm]
private lemma main
  {s' : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  have h' : Tensor α s = Tensor α s' := by rw [h]
  have h : List.Vector α s.prod = List.Vector α s'.prod := by rw [h]
  cast h X.data = (cast h' X).data := by
-- proof
  aesop


-- created on 2025-07-24
