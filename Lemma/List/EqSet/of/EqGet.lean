import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
open List


@[main]
private lemma main
  {s : List α}
  {a : α}
  {d : Fin s.length}
-- given
  (h : s[d] = a) :
-- imply
  s.set d a = s := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength]
  simp [← h]
  grind


-- created on 2026-01-13
