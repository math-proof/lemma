import Lemma.List.DropAppend.eq.Drop.of.LeLength
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakePermute__Neg.eq.Append_RotateDropTake
import Lemma.List.TakeTake.eq.Take.of.Le
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAdd_Min
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMin.of.Lt
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i (-d)).take (i + 1)).drop (i - d + 1) = (s.take i).drop (i - d) := by
-- proof
  have := TakePermute__Neg.eq.Append_RotateDropTake i d
  simp [congrArg (·.drop (i - d + 1)) this]
  rw [DropAppend.eq.Drop.of.LeLength (by simp)]
  simp
  rw [Rotate.eq.AppendDrop__Take.of.GeLength]
  ·
    simp [EqMin.of.Lt (show i - d < s.length by omega)]
    rw [EqAdd_Min.comm]
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp)]
    simp
    rw [TakeDrop.eq.DropTake]
    rw [EqAdd_Min.comm]
    rw [TakeTake.eq.Take.of.Ge (by omega)]
  ·
    simp
    omega


-- created on 2025-10-27
