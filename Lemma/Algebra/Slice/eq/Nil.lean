import stdlib.List
import Lemma.Algebra.Slice.eq.Nil.of.Ge
open Algebra


@[main]
private lemma main
-- given
  (a : List α)
  (i : ℕ) :
-- imply
  a.slice i i = .nil := by
-- proof
  apply Slice.eq.Nil.of.Ge
  simp


-- created on 2025-06-10
