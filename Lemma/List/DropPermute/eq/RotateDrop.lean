import stdlib.List
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Ge_1
import Lemma.Nat.SubSub
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqTake.of.Ge_Length
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.permute i ↑(s.length - 1 - i)).drop i = (s.drop i).rotate 1 := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
  · 
    rw [DropDrop.eq.Drop_Add]
    rw [DropPermute.eq.AppendRotateTakeDrop]
    rw [EqAdd_Sub.of.Ge (by omega)]
    rw [EqAddSub.of.Ge (Ge_1 i)]
    simp
    rw [SubSub.comm]
    rw [EqAddSub.of.Ge (by omega)]
    rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
    · 
      rw [TakeTake.eq.Take.of.Ge (by omega)]
      apply EqAppendS.of.Eq
      rw [EqTake.of.Ge_Length (by simp)]
      simp
    · 
      simp
      omega
  · 
    simp
    omega


-- created on 2025-10-14
