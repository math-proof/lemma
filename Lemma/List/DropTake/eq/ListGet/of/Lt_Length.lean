import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
import Lemma.List.TakeCons.eq.List
import Lemma.List.DropTake.eq.TakeDrop
open List


@[main]
private lemma main
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.take (i + 1)).drop i = [v[i]] := by
-- proof
  rw [DropTake.eq.TakeDrop]
  simp
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length (by assumption)]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
-- updated on 2025-06-20
