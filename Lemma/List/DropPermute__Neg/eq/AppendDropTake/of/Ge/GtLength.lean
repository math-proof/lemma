import Lemma.List.DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add
import Lemma.List.TakeDrop.eq.DropTake
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h_i : s.length > i)
  (h_d : i ≥ d) :
-- imply
  (s.permute ⟨i, h_i⟩ (-d)).drop (i - d + 1) = (s.take i).drop (i - d) ++ s.drop (i + 1) := by
-- proof
  have := DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add (s := s) (i := i - d) (d := d) (by omega)
  simp_all [TakeDrop.eq.DropTake]


-- created on 2025-11-16
