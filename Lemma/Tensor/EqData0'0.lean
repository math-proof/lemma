import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor α s).data = 0 :=
-- proof
  rfl


-- created on 2025-06-22
-- updated on 2026-11-20
