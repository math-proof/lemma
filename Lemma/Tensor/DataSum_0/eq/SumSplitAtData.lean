import sympy.tensor.tensor


@[main, comm]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  (X.sum 0).data = (X.data.splitAt 1).sum := by
-- proof
  rfl


-- created on 2026-07-22
