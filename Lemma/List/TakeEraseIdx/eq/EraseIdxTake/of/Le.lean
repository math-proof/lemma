import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EqTake.of.LeLength
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.TakeAppend.eq.Append_Take.of.LeLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.AddAdd
import Lemma.Nat.EqMin.of.Le
open List Nat


@[main]
private lemma main
-- given
  (h : i ≤ j)
  (a : List α) :
-- imply
  (a.eraseIdx i).take j = (a.take (j + 1)).eraseIdx i := by
-- proof
  if h_i : i < a.length then
    repeat rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [TakeAppend.eq.Append_Take.of.LeLength (by simp; omega)]
    simp
    rw [TakeTake.eq.Take.of.Ge (by omega)]
    simp
    rw [TakeDrop.eq.DropTake]
    rw [EqMin.of.Le (by omega)]
    rw [AddAdd.comm]
    congr
    omega
  else
    simp at h_i
    repeat rw [EqEraseIdx.of.LeLength]
    repeat rw [EqTake.of.LeLength (by omega)]
    repeat omega


-- created on 2025-11-03
