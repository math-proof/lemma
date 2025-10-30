import stdlib.List
import Lemma.List.Rotate.eq.AppendDrop__Take
open List


@[main, comm]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  (s.rotate n).drop (s.length - n % s.length) = s.take (n % s.length) := by
-- proof
  simp [Rotate.eq.AppendDrop__Take]


-- created on 2025-10-19
