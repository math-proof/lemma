module
public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.EqTake.of.LeLength
  {s : List α}
-- given
  (h : s.length ≤ n):
-- imply
  s.take n = s := by
-- proof
  aesop


-- created on 2025-06-16
