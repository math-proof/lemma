import sympy.tensor.tensor


@[main]
private lemma main
  [SubNegMonoid α]
-- given
  (A B : Tensor α s) :
-- imply
  (A - B).data = A.data - B.data :=
-- proof
  rfl


-- created on 2025-12-04
