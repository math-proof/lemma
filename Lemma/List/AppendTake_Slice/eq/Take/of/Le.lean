import stdlib.List
import Lemma.Nat.EqAdd_Sub.of.Ge
open Nat


@[main]
private lemma main
-- given
  (h : i ≤ j)
  (s : List α) :
-- imply
  s.take i ++ s.slice i j = s.take j := by
-- proof
  unfold List.slice List.array_slice Function.comp
  have := s.take_add (i := i) (j := j - i)
  rw [EqAdd_Sub.of.Ge h] at this
  rw [this]


-- created on 2025-06-18
