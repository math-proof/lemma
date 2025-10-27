import Lemma.List.DropTakePermute.eq.RotateTakeDrop
import Lemma.List.EqRotateRotate.of.Add.eq.Length
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Add
open List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s.length > i + d) :
-- imply
  (((s.permute i d).take (i + d + 1)).drop i).rotate d = (s.drop i).take (d + 1) := by
-- proof
  rw [DropTakePermute.eq.RotateTakeDrop]
  rw [EqRotateRotate.of.Add.eq.Length]
  simp
  rw [EqMin.of.Le]
  ·
    apply Add.comm
  ·
    omega


-- created on 2025-10-15
-- updated on 2025-10-23
