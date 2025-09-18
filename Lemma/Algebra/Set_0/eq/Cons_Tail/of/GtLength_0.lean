import Lemma.Algebra.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (a : α) :
-- imply
  s.set 0 a = a :: s.tail := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length h]
  simp


-- created on 2025-07-12
