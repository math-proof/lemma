module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.DropLast.eq.Take_SubLength_1
-- given
  (s : List α) :
-- imply
  s.dropLast = s.take (s.length - 1) := by
-- proof
  apply List.dropLast_eq_take


-- created on 2025-11-24
