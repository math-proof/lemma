import stdlib.List
import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Algebra.LengthTake.eq.Min_Length
import Lemma.Algebra.EqMin.of.Lt
import Lemma.Algebra.EqTakeAppend.of.Eq_Length
open Algebra


@[main]
private lemma main
  {i j : ℕ}
-- given
  (h : i < j)
  (a : List α) :
-- imply
  (a.swap i j).take i = a.take i := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_j
  ·
    rfl
  ·
    simp
    have h_i := Lt.of.Lt.Lt h h_j
    have h_length := LengthTake.eq.Min_Length a i
    have h_min := EqMin.of.Lt h_i
    rw [h_min] at h_length
    apply EqTakeAppend.of.Eq_Length h_length
  ·
    rfl


-- created on 2025-05-17
