import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Add α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  (X + a).data = X.data + a :=
-- proof
  rfl


-- created on 2025-12-01
-- updated on 2026-11-20
