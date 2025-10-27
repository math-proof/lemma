import Lemma.List.TakeDropPermute.eq.TakeDrop
import Lemma.Nat.EqMin.of.Le
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute i d).drop i).take d = (s.drop (i + 1)).take d := by
-- proof
  have := TakeDropPermute.eq.TakeDrop i d
  rwa [EqMin.of.Le (by omega)] at this


-- created on 2025-10-24
-- updated on 2025-10-27
