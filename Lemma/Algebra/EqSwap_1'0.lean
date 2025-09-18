import Lemma.Algebra.EqSwapS
import Lemma.Algebra.EqSwap_0'1
open Algebra


@[main]
private lemma main
-- given
  (a b : α) :
-- imply
  [a, b].swap 1 0 = [b, a] := by
-- proof
  rw [EqSwapS]
  apply EqSwap_0'1


-- created on 2025-06-10
-- updated on 2025-06-16
