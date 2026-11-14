import Theorem.Data.Tensor.Functions


@[path]
private lemma main
  [Log α]
-- given
  (X : Tensor α s) :
-- imply
  (Log.log X).data = Log.log X.data :=
-- proof
  rfl


-- created on 2025-12-04
-- updated on 2026-11-13
