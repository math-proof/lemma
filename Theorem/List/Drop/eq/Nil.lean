module

public import Def.Data.List.List.Basic

public section

public theorem List.Drop.eq.Nil
-- given
  (s : List α) :
-- imply
  s.drop s.length = .nil := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2026-10-26
