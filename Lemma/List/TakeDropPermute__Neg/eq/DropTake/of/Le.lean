import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.TakeDropPermute__Neg.eq.DropTake
import Lemma.Nat.EqSub_Sub.of.Ge
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : d ≤ i) :
-- imply
  ((s.permute i (-d)).drop (i - d + 1)).take d = (s.take i).drop (i - d) := by
-- proof
  have := TakeDropPermute__Neg.eq.DropTake i d
  simp [h] at this
  assumption


@[main, comm]
private lemma sub
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : d ≤ i) :
-- imply
  ((s.permute i (-d)).drop (i + 1 - d)).take d = (s.take i).drop (i - d) := by
-- proof
  rw [SubAdd.eq.AddSub.of.Ge h]
  apply main h


-- created on 2025-10-27
