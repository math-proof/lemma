import Lemma.List.Set.eq.Cons_Set.of.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_i : i > 0)
  (a : α) :
-- imply
  s.set i a = s[0] :: s.tail.set (i - 1) a := by
-- proof
  rw [← Set.eq.Cons_Set.of.GtLength_0 h_s]
  grind


-- created on 2026-07-10
