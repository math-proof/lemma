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


public theorem List.AppendCons.eq.Cons_Append
  (x : α)
  (a b : List α) :
  (x :: a) ++ b = x :: (a ++ b) :=
  (List.Cons_Append.eq.AppendCons x a b).symm


-- created on 2025-06-20
