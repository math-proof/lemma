import Lemma.Algebra.EqTake.of.Ge_Length
import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
open Algebra List


@[main]
private lemma main
-- given
  (h : i ≥ j)
  (a : List α) :
-- imply
  (a.eraseIdx i).take j = a.take j := by
-- proof
  by_cases hlen : j ≤ a.length
  ·
    have h_le_length : j ≤ (a.take i).length := by
      rw [List.length_take]
      exact le_min h hlen
    rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [List.take_append_of_le_length h_le_length, List.take_take, min_eq_left h]
  ·
    rw [EqEraseIdx.of.Ge_Length (by linarith)]


-- created on 2025-10-03
