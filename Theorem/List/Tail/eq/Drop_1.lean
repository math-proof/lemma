module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.Tail.eq.Drop_1
-- given
  (s : List α) :
-- imply
  s.tail = s.drop 1 := by
-- proof
  simp


-- created on 2025-05-05
