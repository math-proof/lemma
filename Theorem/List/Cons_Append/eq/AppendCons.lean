module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.Cons_Append.eq.AppendCons
-- given
  (x : α)
  (a b : List α) :
-- imply
  x :: (a ++ b) = (x ::a) ++ b := by
-- proof
  simp


-- created on 2025-06-20
