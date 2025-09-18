import stdlib.List
import Lemma.Algebra.EqAdd_Sub.of.Ge
open Algebra


@[main]
private lemma main
-- given
  (h : i ≤ j)
  (v : List α) :
-- imply
  v.take i ++ v.slice i j = v.take j := by
-- proof
  unfold List.slice List.array_slice Function.comp
  have := List.take_add v i (j - i)
  rw [EqAdd_Sub.of.Ge h] at this
  rw [this]


-- created on 2025-06-18
