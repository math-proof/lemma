import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.LengthRotate.eq.Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.Nat.EqMin.of.Le
open Nat List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute i d).drop (i + d + 1) = s.drop (i + d + 1) := by
-- proof
  conv_lhs =>
    rw [AddAdd.eq.Add_Add]
  rw [Drop_Add.eq.DropDrop]
  rw [DropPermute.eq.AppendRotateTakeDrop]
  rw [EqDropAppend.of.Eq_Length]
  rw [LengthRotate.eq.Length]
  rw [LengthTake.eq.Min_Length]
  rw [LengthDrop.eq.SubLength]
  rw [EqMin.of.Le]
  omega


-- created on 2025-10-14
