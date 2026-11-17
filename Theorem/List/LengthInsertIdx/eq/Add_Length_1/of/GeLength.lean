module

public import Theorem.Nat.Add
public import Def.Data.List.List.Basic

public section

open Nat


public theorem List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a).length = s.length + 1:=
-- proof
  List.length_insertIdx_of_le_length h a


-- created on 2026-07-12
