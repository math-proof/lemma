import Lemma.List.DropTake.eq.ListGet
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.TakeAppend.eq.Take.of.Le_Length
import Lemma.Nat.Ge_1
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.permute i (-i)).take 1 = [s[i]] := by
-- proof
  simp [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  rw [TakeAppend.eq.Take.of.Le_Length]
  ·
    rw [Rotate.eq.AppendDrop__Take.of.Le_Length (by simp)]
    rw [DropTake.eq.ListGet]
    rw [TakeAppend.eq.Take.of.Le_Length (by simp)]
    simp
  ·
    simp
    apply Ge_1 i


-- created on 2025-10-27
