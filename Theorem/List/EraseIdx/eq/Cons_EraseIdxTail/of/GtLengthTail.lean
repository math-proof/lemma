module

public import Mathlib

public section


public theorem List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail
  {s : List α}
-- given
  (h : i < s.tail.length)
  (default : α):
-- imply
  s.eraseIdx i.succ = s.headD default :: s.tail.eraseIdx i := by
-- proof
  cases s
  ·
    contradiction
  ·
    rfl


-- created on 2025-06-09
