import stdlib.List
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.Rotate.eq.AppendDrop__Take.of.Lt_Length
open Algebra


@[main]
private lemma main
  {v : List α}
  {n : ℕ}
-- given
  (h : n ≤ v.length) :
-- imply
  v.rotate n = v.drop n ++ v.take n := by
-- proof
  by_cases h_n : n = v.length
  ·
    rw [h_n]
    simp
  ·
    have h := Lt.of.Le.Ne h_n h
    apply Rotate.eq.AppendDrop__Take.of.Lt_Length h


-- created on 2025-06-17
