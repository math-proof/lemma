module

public import Mathlib

public section


public theorem List.Append.of.Eq.left
  {a b : List α}
-- given
  (h : a = b)
  (c : List α) :
-- imply
  c ++ a = c ++ b := by
-- proof
  rw [h]


public theorem List.Append.of.Eq
  {a b c : List α}
-- given
  (h : a = b) :
-- imply
  a ++ c = b ++ c := by
-- proof
  rw [h]


-- created on 2025-06-17
