import Lemma.Vector.Sum.eq.SumVal
import Lemma.Vector.ValAppend.eq.AppendValS
open Vector


@[main, comm]
private lemma main
  [AddMonoid α]
-- given
  (a : List.Vector α m)
  (b : List.Vector α n) :
-- imply
  (a ++ b).sum = a.sum + b.sum := by
-- proof
  simp [Sum.eq.SumVal]
  simp [ValAppend.eq.AppendValS]


-- created on 2026-07-22
