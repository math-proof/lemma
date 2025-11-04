import stdlib.List
import Lemma.List.Slice.eq.Nil.of.Gt
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : stop ≥ a.length) :
-- imply
  a.slice start stop = a.slice start a.length := by
-- proof
  if h : start ≤ stop then
    unfold List.slice List.array_slice
    simp_all
  else
    simp at h
    rw [Slice.eq.Nil.of.Gt h]
    rw [Slice.eq.Nil.of.Gt]
    linarith


-- created on 2025-06-07
