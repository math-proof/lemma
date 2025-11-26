import Lemma.List.DropTake.eq.ListGet
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.DropTakePermute__Neg.eq.RotateDropTake
import Lemma.List.EqPermuteS__Neg.of.Ge
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakePermute__Neg.eq.ListGet
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Sub.eq.Zero.of.Lt
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
import Lemma.Nat.Sub_Sub.eq.Min
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i (-d)).take (i - d + 1)).drop (i - d) = [s[i]] := by
-- proof
  if h_d : d ≤ i then
    have h := DropTakePermute__Neg.eq.RotateDropTake i d
    rw [DropTake.eq.TakeDrop] at h ⊢
    rw [SubAdd.eq.AddSub.of.Ge (by omega)] at h
    rw [Sub_Sub.eq.Min] at h
    rw [EqSubAdd.left]
    have h := congrArg (·.take 1) h
    simp at h
    rw [TakeTake.eq.Take.of.Ge (by omega)] at h
    rw [h]
    rw [EqMin.of.Le h_d]
    rw [Rotate.eq.AppendDrop__Take.of.GeLength] <;>
      simp
    ·
      rw [EqAddSub.of.Ge h_d]
      rw [DropTake.eq.ListGet]
      rw [TakeAppend.eq.Take.of.GeLength (by simp)]
      simp
    ·
      omega
  else
    simp at h_d
    rw [EqPermuteS__Neg.of.Ge (by omega)]
    simp [Sub.eq.Zero.of.Lt h_d]
    apply TakePermute__Neg.eq.ListGet


-- created on 2025-10-27
