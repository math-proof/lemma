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


public theorem List.AddLengthS.eq.LengthAppend
  (a b : List α) :
  a.length + b.length = (a ++ b).length :=
  (List.LengthAppend.eq.AddLengthS a b).symm


-- created on 2025-05-08
