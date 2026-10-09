import Lemma.List.Rotate.eq.AppendDrop__Take.of.GtLength
open List


@[path]
private lemma main
-- given
  (a b : α) :
-- imply
  [a, b].rotate 1 = [b, a] := by
-- proof
  rw [Rotate.eq.AppendDrop__Take.of.GtLength]
  repeat simp


-- created on 2025-07-18
