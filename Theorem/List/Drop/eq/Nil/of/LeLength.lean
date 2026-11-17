module

public import Def.Data.List.List.Basic

public section

public theorem List.Drop.eq.Nil.of.LeLength
  {s : List α}
-- given
  (h : s.length ≤ i) :
-- imply
  s.drop i = [] := by
-- proof
  simp_all


-- created on 2025-06-07
