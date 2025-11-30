import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
open List


@[main]
private lemma main
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.eraseIdx i).take j = s.take j := by
-- proof
  if h_j : j ≤ s.length then
    have h_le_length : j ≤ (s.take i).length := by
      rw [List.length_take]
      exact le_min h h_j
    rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [List.take_append_of_le_length h_le_length, List.take_take, min_eq_left h]
  else
    rw [EqEraseIdx.of.LeLength (by linarith)]


-- created on 2025-10-03
-- updated on 2025-11-04
