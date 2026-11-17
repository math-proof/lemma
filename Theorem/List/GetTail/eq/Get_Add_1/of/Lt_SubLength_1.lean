module

public import Initialize.Tactic.Attr.Basic

public section


@[fin]
public theorem List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  s.tail[i]'(by simpa) = s[i + 1] := by
-- proof
  grind


-- created on 2025-10-05
