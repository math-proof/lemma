module

public import Def.Data.List.List.Basic

public section

public theorem List.LengthEnumerate.eq.Length
-- given
  (s : List α) :
-- imply
  s.enumerate.length = s.length := by
-- proof
  simp [List.enumerate]


-- created on 2025-06-02
