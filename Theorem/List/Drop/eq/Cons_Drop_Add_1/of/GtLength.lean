module

public import Mathlib

public section


public theorem List.Drop.eq.Cons_Drop_Add_1.of.GtLength
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s.drop i = s[i] :: s.drop (i + 1) :=
-- proof
  List.drop_eq_getElem_cons h


-- created on 2025-06-14
