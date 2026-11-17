module

public import Def.Data.List.List.Basic

public section

public theorem List.Slice_0.eq.Take
-- given
  (s : List α) :
-- imply
  s.slice 0 n = s.take n := by
-- proof
  unfold List.slice List.array_slice Function.comp
  simp


-- created on 2025-06-18
