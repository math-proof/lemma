module

public import Theorem.List.EqTake.of.LeLength
public import Theorem.List.LengthSet.eq.Length
public import Theorem.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
public import Theorem.List.TakeAppend.eq.Append_Take.of.LeLength
public import Theorem.List.TakeCons.eq.Cons_Take.of.Gt_0
public import Theorem.List.TakeDrop.eq.DropTake
public import Theorem.List.TakeTake.eq.Take.of.Ge
public import Theorem.Nat.EqAdd_Sub.of.Ge
public import Theorem.Nat.EqMin.of.Le
public import Theorem.Nat.Sub_Add.eq.SubSub

public section

open List Nat


public theorem List.TakeSet.eq.SetTake.of.Lt
  {s : List α}
-- given
  (h : i < j)
  (a : α) :
-- imply
  (s.set i a).take j = (s.take j).set i a := by
-- proof
  if h_j : j ≤ s.length then
    rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by omega)]
    rw [TakeAppend.eq.Append_Take.of.LeLength]
    ·
      rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by simp; omega)]
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
    repeat rw [EqTake.of.LeLength]
    ·
      omega
    ·
      rw [LengthSet.eq.Length]
      omega


-- created on 2025-11-18
