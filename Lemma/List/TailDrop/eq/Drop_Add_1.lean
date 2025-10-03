import stdlib.Slice
import Lemma.List.Tail.eq.Drop_1
open List


@[main]
private lemma main
  {s : List α} :
-- imply
  (s.drop i).tail = s.drop (i + 1) := by
-- proof
  rw [Tail.eq.Drop_1]
  simp


-- created on 2025-05-05
