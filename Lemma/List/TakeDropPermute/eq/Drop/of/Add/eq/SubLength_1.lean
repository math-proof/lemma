import Lemma.List.TakeRotateDrop.eq.Drop
import Lemma.List.DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  ((s.permute i d).drop i).take d = s.drop (i + 1) := by
-- proof
  rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (by simp [h])]
  rw [← TakeRotateDrop.eq.Drop i]
  grind


-- created on 2025-10-23
