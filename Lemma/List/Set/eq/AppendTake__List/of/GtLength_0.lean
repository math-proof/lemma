import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (a : α) :
-- imply
  s.set (s.length - 1) a = s.take (s.length - 1) ++ [a] := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength]
  .
    grind
  .
    simpa


-- created on 2026-07-04
