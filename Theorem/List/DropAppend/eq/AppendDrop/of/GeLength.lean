module

public import Mathlib

public section


public theorem List.DropAppend.eq.AppendDrop.of.GeLength
-- given
  (h : a.length ≥ i)
  (b : List α) :
-- imply
  (a ++ b).drop i = a.drop i ++ b :=
-- proof
  List.drop_append_of_le_length h


-- created on 2025-06-20
-- updated on 2026-10-26
