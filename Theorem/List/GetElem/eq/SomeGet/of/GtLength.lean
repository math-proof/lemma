module

public import Def.Data.List.List.Basic

public section

public theorem List.GetElem.eq.SomeGet.of.GtLength
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i]? = some s[i] := by
-- proof
  simp [h]


-- created on 2025-05-15
