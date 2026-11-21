import Instance.Data.Tensor.Defs.Part3
import Instance.Data.Tensor.Tensor.Part2


@[path]
private lemma main
-- given
  (x : α) :
-- imply
  (x : Tensor α []).data.head = x := by
-- proof
  rfl

@[path]
private lemma nat
  [NatCast α]
-- given
  (x : ℕ) :
-- imply
  (x : Tensor α []).data.head = x := by
-- proof
  rfl


-- created on 2025-12-30
-- updated on 2026-11-20
