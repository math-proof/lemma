import Lemma.List.DropPermute.eq.RotateDrop
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.permute i ↑(s.length - 1 - i)).drop (s.length - 1) = [s[i]] := by
-- proof
  have h := DropPermute.eq.RotateDrop i
  have h := congrArg (·.drop (s.length - 1 - i)) h
  simp only [DropDrop.eq.Drop_Add] at h
  rw [EqAdd_Sub.of.Ge (show i ≤ s.length - 1 by omega)] at h
  rw [h]
  rw [Rotate.eq.AppendDrop__Take.of.Le_Length (by grind)]
  rw [EqDropAppend.of.Eq_Length (by grind)]
  apply TakeDrop.eq.ListGet.of.Lt_Length


-- created on 2025-10-13
-- updated on 2025-10-23
