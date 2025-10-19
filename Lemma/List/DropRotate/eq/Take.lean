import stdlib.List
import Lemma.List.Rotate.eq.AppendDrop__Take
open List


@[main, comm]
private lemma main
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  (v.rotate n).drop (v.length - n % v.length) = v.take (n % v.length) := by
-- proof
  simp [Rotate.eq.AppendDrop__Take]


-- created on 2025-10-19
