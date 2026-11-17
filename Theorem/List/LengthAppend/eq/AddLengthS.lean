module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.LengthAppend.eq.AddLengthS
-- given
  (a b : List α) :
-- imply
  (a ++ b).length = a.length + b.length := by
-- proof
  apply List.length_append


-- created on 2025-05-08
