import Lemma.Nat.SubSub
import Lemma.List.DropPermute.eq.RotateDrop
import Lemma.List.EqRotateRotate.of.Le_Length.Eq_Length
open Nat List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  ((s.permute i ↑(s.length - 1 - i)).drop i).rotate (s.length - 1 - i) = s.drop i := by
-- proof
  rw [DropPermute.eq.RotateDrop]
  rw [SubSub.comm]
  rw [EqRotateRotate.of.Le_Length.Eq_Length] <;>
    simp
  omega


-- created on 2025-10-12
-- updated on 2025-10-14
