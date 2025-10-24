import Lemma.List.TakeAppend.eq.AppendTakeS
import Lemma.Nat.Sub.eq.Zero.of.Le
open List Nat


@[main]
private lemma main
-- given
  (h : i ≤ a.length)
  (b : List α) :
-- imply
  (a ++ b).take i = a.take i := by
-- proof
  rw [TakeAppend.eq.AppendTakeS]
  simp [Sub.eq.Zero.of.Le h]


-- created on 2025-10-24
