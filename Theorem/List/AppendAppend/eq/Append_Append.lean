module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.AppendAppend.eq.Append_Append
-- given
  (a b c : List α) :
-- imply
  a ++ b ++ c = a ++ (b ++ c) :=
-- proof
  List.append_assoc a b c


-- created on 2025-05-17
