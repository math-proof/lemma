import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.SetCons.eq.Cons_Set
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (i : ℕ)
  (a : α) :
-- imply
  s.set (i + 1) a = s[0] :: s.tail.set i a := by
-- proof
  rw [Cons_Set.eq.SetCons]
  rw [EqCons_Tail.of.GtLength_0 h_s]


-- created on 2026-07-10
