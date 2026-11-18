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


public theorem List.Drop_1.eq.Tail
  (s : List α) :
  s.drop 1 = s.tail :=
  (List.Tail.eq.Drop_1 s).symm

-- created on 2025-05-05
