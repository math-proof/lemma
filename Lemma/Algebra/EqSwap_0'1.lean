import stdlib.List
import Lemma.Algebra.Swap.eq.Ite
import Lemma.Algebra.Slice.eq.Nil
open Algebra


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
