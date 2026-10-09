import Lemma.List.Rotate.eq.AppendDrop__Take
open List


@[path]
private lemma main
-- given
  (s : List α) :
-- imply
  s.rotate 0 = s := by
-- proof
  simp [Rotate.eq.AppendDrop__Take]


-- created on 2025-10-19
