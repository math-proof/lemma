import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).data = X.data / n.data[0] := by
-- proof
  aesop


-- created on 2025-09-24
-- updated on 2026-11-20
