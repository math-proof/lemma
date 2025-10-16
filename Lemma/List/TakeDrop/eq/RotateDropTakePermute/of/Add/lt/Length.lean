import Lemma.List.RotateTakeDrop.eq.DropTakePermute.of.Add.lt.Length
import Lemma.List.EqRotateRotate.of.Add.eq.Length
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Add
open List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d < s.length) :
-- imply
  (s.drop i).take (d + 1) = (((s.permute i d).take (d + i + 1)).drop i).rotate d := by
-- proof
  rw [DropTakePermute.eq.RotateTakeDrop.of.Add.lt.Length h]
  rw [EqRotateRotate.of.Add.eq.Length]
  simp
  rw [EqMin.of.Le]
  ·
    apply Add.comm
  ·
    omega


-- created on 2025-10-15
