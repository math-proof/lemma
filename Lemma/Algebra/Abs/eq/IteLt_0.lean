import Lemma.Algebra.Abs.eq.IteGe_0
import Lemma.Logic.Ite.eq.IteNot
open Algebra Logic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (x : α) :
-- imply
  |x| = if x < 0 then
    -x
  else
    x := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Abs.eq.IteGe_0]
  simp


-- created on 2025-04-17
-- updated on 2025-10-01
