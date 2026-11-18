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



public theorem List.Append_Append.eq.AppendAppend
  (a b c : List α) :
  a ++ (b ++ c) = a ++ b ++ c :=
  (List.AppendAppend.eq.Append_Append a b c).symm

-- created on 2025-05-17
