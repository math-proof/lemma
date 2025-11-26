import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.TakeTake.eq.Take.of.Le
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMin.of.Le
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i d).drop i).take (d ⊓ (s.length - i - 1)) = (s.drop (i + 1)).take d := by
-- proof
  have := DropPermute.eq.AppendRotateTakeDrop i d
  if h : s.length > i + d then
    rw [EqMin.of.Le (by omega)]
    have := congrArg (·.take d) this
    simp at this
    rw [this]
    rw [TakeAppend.eq.Take.of.GeLength]
    ·
      rw [Rotate.eq.AppendDrop__Take.of.GeLength]
      ·
        rw [TakeAppend.eq.Take.of.GeLength]
        ·
          rw [TakeDrop.eq.DropTake]
          rw [TakeTake.eq.Take.of.Le (by omega)]
          simp [TakeDrop.eq.DropTake]
          rw [Add.comm (a := d)]
          rw [Add_Add.eq.AddAdd]
        ·
          simp
          rw [EqMin.of.Le (by omega)]
          simp
      ·
        simp
        omega
    ·
      simp
      omega
  else
    simp at h
    have := congrArg (·.take (s.length - i)) this
    simp at this
    rw [EqPermuteS.of.Add.ge.SubLength_1 (by omega)] at this ⊢
    rw [EqTake.of.Ge_Length (by simp)] at this
    rw [this]
    rw [Drop.eq.Nil.of.Ge_Length (i := i + d + 1) (by simp; omega)]
    simp
    rw [EqMin.of.Ge (by simp; omega)]
    rw [EqTake.of.Ge_Length (n := s.length - i) (by simp)]
    rw [Rotate.eq.AppendDrop__Take.of.GeLength (by simp; omega)]
    rw [TakeTake.eq.Take.of.Ge (by simp)]
    rw [TakeDrop.eq.DropTake]
    simp
    rw [TakeAppend.eq.Take.of.GeLength]
    ·
      rw [EqTake.of.Ge_Length]
      ·
        rw [DropTake.eq.TakeDrop]
        simp
        omega
      ·
        simp
        omega
    ·
      simp
      omega


-- created on 2025-10-24
-- updated on 2025-10-27
