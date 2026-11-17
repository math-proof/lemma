module

public import Theorem.List.DropAppend.eq.Drop.of.LeLength
public import Theorem.List.DropCons.eq.Drop_Sub_1.of.Gt_0
public import Theorem.List.LengthSet.eq.Length
public import Theorem.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
public import Theorem.Nat.EqAdd_Sub.of.Ge
public import Theorem.Nat.EqMin.of.Le
public import Theorem.Nat.Sub_Add.eq.SubSub

public section

open List Nat


public theorem List.DropSet.eq.Drop.of.Lt
-- given
  (h : i < j)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).drop j = s.drop j := by
-- proof
  if h_j : j ≤ s.length then
    rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by omega)]
    rw [DropAppend.eq.Drop.of.LeLength]
    ·
      rw [DropCons.eq.Drop_Sub_1.of.Gt_0]
      ·
        simp
        rw [EqMin.of.Le (by omega)]
        omega
      ·
        simp
        left
        omega
    ·
      simp
      left
      omega
  else
    repeat rw [Drop.eq.Nil.of.LeLength]
    repeat grind


-- created on 2025-11-18
