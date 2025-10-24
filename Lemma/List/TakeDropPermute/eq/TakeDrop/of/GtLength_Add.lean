import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.TakeAppend.eq.Take.of.Le_Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Le
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute i d).drop i).take d = (s.drop (i + 1)).take d := by
-- proof
  have := DropPermute.eq.AppendRotateTakeDrop i d
  have := congrArg (·.take d) this
  simp at this
  rw [this]
  rw [TakeAppend.eq.Take.of.Le_Length]
  ·
    rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
    ·
      rw [TakeAppend.eq.Take.of.Le_Length]
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


-- created on 2025-10-24
