import stdlib.List
import Lemma.Algebra.EqSubAdd
open Algebra


@[main]
private lemma main
-- given
  (v : List α) :
-- imply
  (v.drop i).take d = v.slice i (i + d) := by
-- proof
  unfold List.slice List.array_slice Function.comp
  rw [EqSubAdd.left.int]


-- created on 2025-06-18
