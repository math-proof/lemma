import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.LengthSet.eq.Length
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.TakeAppend.eq.Append_Take.of.Ge_Length
import Lemma.List.TakeCons.eq.Cons_Take.of.Gt_0
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Sub_Add.eq.SubSub
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < j)
  (a : α) :
-- imply
  (s.set i a).take j = (s.take j).set i a := by
-- proof
  if h_j : j ≤ s.length then
    rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length (by omega)]
    rw [TakeAppend.eq.Append_Take.of.Ge_Length]
    ·
      rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length (by simp; omega)]
      rw [TakeTake.eq.Take.of.Ge (by omega)]
      simp
      rw [EqMin.of.Le (by omega)]
      rw [TakeCons.eq.Cons_Take.of.Gt_0 (by omega)]
      rw [TakeDrop.eq.DropTake]
      rw [SubSub.eq.Sub_Add]
      rw [EqAdd_Sub.of.Ge (by omega)]
    ·
      simp
      left
      omega
  else
    repeat rw [EqTake.of.Ge_Length]
    ·
      omega
    ·
      rw [LengthSet.eq.Length]
      omega


-- created on 2025-11-18
