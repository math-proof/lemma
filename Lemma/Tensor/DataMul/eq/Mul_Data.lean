import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Mul α]
-- given
  (a : α)
  (X : Tensor α s) :
-- imply
  (a * X).data = a * X.data :=
-- proof
  rfl


-- created on 2026-01-06
-- updated on 2026-11-20
