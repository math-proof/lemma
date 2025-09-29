import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor α s).data = 0 :=
-- proof
  rfl


-- created on 2025-06-22
