import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.DropTakePermute__Neg.eq.DropTake
import Lemma.Nat.MinMin.eq.Min_Min
import Lemma.Nat.Sub_Sub.eq.Min
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  -- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i (-d)).drop (i - d + 1)).take (i ⊓ d) = (s.take i).drop (i - d) := by
-- proof
  rw [← DropTakePermute__Neg.eq.DropTake]
  rw [DropTake.eq.TakeDrop]
  simp
  rw [Sub_Sub.eq.Min]
  apply Min_Min.eq.MinMin


-- created on 2025-10-27
