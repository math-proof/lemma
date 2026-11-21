import Instance.Data.Tensor.Tensor


@[path]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X.get i = X[i] := by
-- proof
  rfl


-- created on 2025-07-12
-- updated on 2026-11-20
