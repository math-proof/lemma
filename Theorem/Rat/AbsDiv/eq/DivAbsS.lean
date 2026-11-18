module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Rat.AbsDiv.eq.DivAbsS
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  |a / b| = |a| / |b| :=
-- proof
  abs_div a b


-- created on 2025-12-09
