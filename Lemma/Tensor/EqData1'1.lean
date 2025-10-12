import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [One α]
-- given
  (s : List ℕ) :
-- imply
  (1 : Tensor α s).data = 1 :=
-- proof
  rfl


-- created on 2025-10-12
