import Lemma.List.TakePermute.eq.RotateTake.of.Lt_Length
import Lemma.List.DropRotate.eq.Take.of.EqLength_Add
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.Take_1.eq.ListGet_0.of.GtLength_0
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Add
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : d < s.length) :
-- imply
  ((s.permute ⟨0, by linarith⟩ d).take (d + 1)).drop d = [s[0]] := by
-- proof
  rw [TakePermute.eq.RotateTake.of.Lt_Length h]
  rw [DropRotate.eq.Take.of.EqLength_Add]
  ·
    rw [TakeTake.eq.Take.of.Ge (by simp)]
    rw [Take_1.eq.ListGet_0.of.GtLength_0]
  ·
    rw [LengthTake.eq.Min_Length]
    rw [Add.comm]
    rw [EqMin.of.Le]
    omega


-- created on 2025-10-22
