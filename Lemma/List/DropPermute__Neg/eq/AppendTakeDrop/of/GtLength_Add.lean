import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropPermute__Neg.eq.Drop
import Lemma.List.EqAppendS.of.Eq.Eq
import Lemma.List.TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add
import Lemma.Nat.AddAdd
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute ⟨i + d, by grind⟩ (-d)).drop (i + 1) = (s.drop i).take d ++ s.drop (i + d + 1) := by
-- proof
  have h_take := TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add h
  have h_drop := DropPermute__Neg.eq.Drop (s := s) ⟨i + d, by grind⟩ d
  simp at h_drop
  rw [AddAdd.comm] at h_drop
  rw [Drop_Add.eq.DropDrop] at h_drop
  have h := EqAppendS.of.Eq.Eq h_take h_drop
  simp at h
  rw [AddAdd.comm] at h
  assumption


-- created on 2025-10-29
