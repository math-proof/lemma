import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.TakeAppend.eq.Append_Take.of.Ge_Length
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
  by_cases h_i : i < a.length
  ·
    repeat rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [TakeAppend.eq.Append_Take.of.Ge_Length (by simp; omega)]
    simp
    rw [TakeTake.eq.Take.of.Ge (by omega)]
    simp
    rw [TakeDrop.eq.DropTake]
    rw [EqMin.of.Le (by omega)]
    rw [AddAdd.comm]
    congr
    omega
  ·
    simp at h_i
    repeat rw [EqEraseIdx.of.Ge_Length (by simp; omega)]
    repeat rw [EqTake.of.Ge_Length (by omega)]


-- created on 2025-11-03
