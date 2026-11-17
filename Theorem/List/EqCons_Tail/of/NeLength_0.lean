module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.EqCons_Tail.of.NeLength_0
  {s : List α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s[0] :: s.tail = s:= by
-- proof
  cases s
  ·
    contradiction
  ·
    rfl


-- created on 2024-07-01
-- updated on 2026-10-26
