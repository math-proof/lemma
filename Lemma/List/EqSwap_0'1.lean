import stdlib.List
import Lemma.List.Swap.eq.Ite
import Lemma.List.Slice.eq.Nil
open List


@[main]
private lemma main
-- given
  (a b : α) :
-- imply
  [a, b].swap 0 1 = [b, a] := by
-- proof
  rw [Swap.eq.Ite]
  simp
  apply Slice.eq.Nil


-- created on 2025-06-16
