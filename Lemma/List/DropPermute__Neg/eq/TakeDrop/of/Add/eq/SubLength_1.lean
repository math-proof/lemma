import Initialize.Tactic.Attr.Basic
import Lemma.List.TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add
import Theorem.Data.List.List.Part2
open List


@[path, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  ((s.permute ⟨i + d, by grind⟩ (-d)).drop (i + 1)) = (s.drop i).take d := by
-- proof
  have := TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add (s := s) (i := i) (d := d) (by omega)
  rwa [EqTake.of.LeLength] at this
  simp [List.length_permute]
  omega


-- created on 2025-10-28
