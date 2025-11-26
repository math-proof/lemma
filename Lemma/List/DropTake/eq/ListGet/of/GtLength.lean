import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.List.TakeCons.eq.List
import Lemma.List.DropTake.eq.TakeDrop
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  rw [DropTake.eq.TakeDrop]
  simp
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by assumption)]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
-- updated on 2025-06-20
