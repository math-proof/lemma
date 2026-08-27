import Lemma.Vector.GetMap.eq.UFnGet
open Vector


@[main, fin]
private lemma main
  {β : Type*}
-- given
  (h : i < n)
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (v.map f)[i] = f v[i] := by
-- proof
  apply GetMap.eq.UFnGet


-- created on 2025-06-01
-- updated on 2026-08-27
