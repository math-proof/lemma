import Lemma.List.DropTake.eq.ListGet
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.TakeAppend.eq.Take.of.GeLength
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
  simp [Permute__Neg.eq.Append_AppendRotateDropTake.simp]
  rw [TakeAppend.eq.Take.of.GeLength]
  ·
    rw [Rotate.eq.AppendDrop__Take.of.GeLength (by simp)]
    rw [DropTake.eq.ListGet]
    rw [TakeAppend.eq.Take.of.GeLength (by simp)]
    simp
  ·
    simp
    apply Ge_1 i


-- created on 2025-10-27
