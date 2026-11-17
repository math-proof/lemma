module
public import Mathlib

public section


public theorem List.EqTakeAppend
-- given
  (a b : List α) :
-- imply
  (a ++ b).take a.length = a := by
-- proof
  aesop


-- created on 2025-05-11
