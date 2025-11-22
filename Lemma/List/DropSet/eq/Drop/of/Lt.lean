import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropAppend.eq.Drop.of.Ge_Length
import Lemma.List.DropCons.eq.Drop_Sub_1.of.Gt_0
import Lemma.List.LengthSet.eq.Length
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Sub_Add.eq.SubSub
open List Nat


@[main]
private lemma main
-- given
  (h : i < j)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).drop j = s.drop j := by
-- proof
  if h_j : j ≤ s.length then
    rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length (by omega)]
    rw [DropAppend.eq.Drop.of.Ge_Length]
    ·
      rw [DropCons.eq.Drop_Sub_1.of.Gt_0]
      ·
        simp
        rw [EqMin.of.Le (by omega)]
        rw [SubSub.eq.Sub_Add]
        rw [EqAdd_Sub.of.Ge (by omega)]
      ·
        simp
        left
        omega
    ·
      simp
      left
      omega
  else
    repeat rw [Drop.eq.Nil.of.Ge_Length]
    repeat grind


-- created on 2025-11-18
