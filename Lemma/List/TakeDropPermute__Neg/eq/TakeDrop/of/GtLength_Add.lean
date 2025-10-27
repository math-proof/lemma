import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeDropPermute__Neg.eq.DropTake
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute ⟨i + d, h⟩ (-d)).drop (i + 1)).take d = (s.drop i).take d := by
-- proof
  have := TakeDropPermute__Neg.eq.DropTake ⟨i + d, h⟩ d
  simp at this
  rw [this]
  rw [TakeDrop.eq.DropTake]


-- created on 2025-10-27
