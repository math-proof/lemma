import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TakeAppend.eq.Append_Take.of.LeLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqMin.of.Lt
open List Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : s.length > 1) :
-- imply
  ((s.take (d + 1)).rotate 1).tail = ((s.eraseIdx 1).take d).rotate 1 := by
-- proof
  have h_d := NeZero.pos d
  repeat rw [Rotate.eq.AppendDrop__Take.of.GeLength]
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
    repeat rw [TakeTake.eq.Take.of.Ge (by omega)]
    rw [TakeEraseIdx.eq.Take.of.Ge (j := 1) (by omega)]
    simp
    rw [TailTake.eq.TakeTail]
    rw [EraseIdx.eq.Append_Drop_Add_1]
    simp
    rw [TakeAppend.eq.Append_Take.of.LeLength (by simp; omega)]
    simp [EqMin.of.Lt h]
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
    rw [TailTake.eq.TakeTail]
    simp [TakeDrop.eq.DropTake]
    rw [show (2 + (d - 1)) = 1 + d by omega]
    repeat rw [Tail.eq.Drop_1]
    rw [TakeDrop.eq.DropTake]
    simp
  ·
    simp
    rw [LengthEraseIdx.eq.SubLength_1.of.GtLength (by omega)]
    omega
  ·
    simp
    omega


-- created on 2025-11-03
