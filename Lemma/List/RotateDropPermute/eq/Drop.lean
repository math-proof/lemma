import Lemma.List.Rotate.eq.AppendDrop__Take.of.Lt_Length
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Nat.SubSub
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i ↑(s.length - i - 1)).drop i).rotate (s.length - i - 1) = s.drop i := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.Lt_Length]
  ·
    rw [DropDrop.eq.Drop_Add]
    rw [SubSub.comm]
    rw [EqAdd_Sub.of.Ge (by omega)]
    sorry
  ·
    rw [LengthDrop.eq.SubLength]
    rw [LengthPermute.eq.Length]
    sorry


-- created on 2025-10-12
