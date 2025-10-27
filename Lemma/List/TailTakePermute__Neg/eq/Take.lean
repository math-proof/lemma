import Lemma.List.DropTakePermute__Neg.eq.DropTake
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  ((s.permute i (-i)).take (i + 1)).tail = s.take i := by
-- proof
  have := DropTakePermute__Neg.eq.DropTake i i
  simp at this
  assumption


-- created on 2025-10-27
