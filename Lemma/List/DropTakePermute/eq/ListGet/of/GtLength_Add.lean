import Lemma.List.DropTakePermute.eq.RotateTakeDrop
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.TakeDrop.eq.ListGet.of.GtLength
open List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute i d).take (i + d + 1)).drop (i + d) = [s[i]] := by
-- proof
  have h := DropTakePermute.eq.RotateTakeDrop i d
  have h := congrArg (·.drop d) h
  simp at h
  rw [Rotate.eq.AppendDrop__Take.of.GeLength] at h
  ·
    rw [EqDropAppend.of.Eq_Length] at h
    ·
      rw [h]
      rw [TakeTake.eq.Take.of.Ge (by omega)]
      apply TakeDrop.eq.ListGet.of.GtLength
    ·
      simp
      rw [EqMin.of.Le]
      ·
        simp
      ·
        omega
  ·
    simp
    omega


-- created on 2025-10-24
