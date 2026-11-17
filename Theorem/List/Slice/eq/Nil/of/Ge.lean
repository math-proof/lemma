module

public import Def.Data.List.List.Basic

public section

public theorem List.Slice.eq.Nil.of.Ge
  {s : List α}
-- given
  (h : start ≥ stop) :
-- imply
  s.slice start stop = .nil := by
-- proof
  unfold List.slice List.array_slice
  simp_all


-- created on 2025-06-07
