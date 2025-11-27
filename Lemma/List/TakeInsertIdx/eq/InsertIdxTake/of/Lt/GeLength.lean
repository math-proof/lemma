import Lemma.Nat.SubSub
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EqLengthTake.of.GeLength
import Lemma.List.InsertIdx.eq.Append_Cons.of.GeLength
import Lemma.List.TakeAppend.eq.Append_Take.of.LeLength
import Lemma.List.TakeCons.eq.Cons_Take.of.Gt_0
import Lemma.List.TakeTake.eq.Take.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length ≥ i)
  (h_j : i < j)
  (x : α) :
-- imply
  (s.insertIdx i x).take j = (s.take (j - 1)).insertIdx i x := by
-- proof
  repeat rw [InsertIdx.eq.Append_Cons.of.GeLength]
  ·
    rw [TakeAppend.eq.Append_Take.of.LeLength (by simp; omega)]
    rw [EqLengthTake.of.GeLength h_i]
    rw [TakeTake.eq.Take.of.Ge (by omega)]
    simp
    rw [TakeCons.eq.Cons_Take.of.Gt_0 (by omega)]
    simp
    rw [DropTake.eq.TakeDrop]
    rw [SubSub.comm]
  ·
    simp
    omega
  ·
    assumption


-- created on 2025-11-27
