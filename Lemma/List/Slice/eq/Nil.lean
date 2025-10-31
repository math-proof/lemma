import stdlib.List
import Lemma.List.Slice.eq.Nil.of.Ge
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.slice i i = .nil := by
-- proof
  apply Slice.eq.Nil.of.Ge
  simp


-- created on 2025-06-10
