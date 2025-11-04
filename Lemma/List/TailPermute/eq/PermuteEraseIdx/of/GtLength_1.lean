import Lemma.List.DropAppend.eq.Drop.of.Ge_Length
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TakeAppend.eq.Take.of.Le_Length
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqMin.of.Lt
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 1)
  (d : ℕ):
-- imply
  (s.permute ⟨0, by omega⟩ ↑(d + 1)).tail = (s.eraseIdx 1).permute ⟨0, by rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by omega)]; omega⟩ d := by
-- proof
  repeat rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
  rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
  repeat rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
    rw [Tail.eq.Drop_1]
    simp
    rw [show d + 1 + 1 = 2 + d by omega]
    rw [DropTake.eq.TakeDrop]
    simp
    repeat rw [TakeTake.eq.Take.of.Ge (by omega)]
    rw [EraseIdx.eq.Append_Drop_Add_1]
    simp
    rw [TailTake.eq.TakeTail]
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simp; omega)]
    simp [TailTake.eq.TakeTail]
    rw [TakeAppend.eq.Take.of.Le_Length (by simp; omega)]
    rw [TakeTake.eq.Take.of.Ge (by omega)]
    simp
    rw [DropAppend.eq.Drop.of.Ge_Length (by simp)]
    simp
    rw [EqMin.of.Lt h]
    simp
  ·
    simp
    rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by omega)]
    omega
  ·
    simp
    omega


@[main]
private lemma pos
  [NeZero (d : ℕ)]
  {s : List α}
-- given
  (h : s.length > 1) :
-- imply
  (s.permute ⟨0, by omega⟩ d).tail = (s.eraseIdx 1).permute ⟨0, by rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by omega)]; omega⟩ ↑(d - 1) := by
-- proof
  rw [← TailPermute.eq.PermuteEraseIdx.of.GtLength_1 (s := s) (d := d - 1) (by omega)]
  congr
  have h_d := NeZero.pos d
  omega


-- created on 2025-11-03
