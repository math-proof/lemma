import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
open List


@[main]
private lemma fin
  {v : List α}
-- given
  (h : j < v.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  (v.insertIdx i a).get ⟨j, h.trans_le List.length_le_length_insertIdx⟩ = v.get ⟨j, h⟩ := by
-- proof
  apply List.get_insertIdx_of_lt
  assumption


@[main]
private lemma main
  {v : List α}
-- given
  (h : j < v.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  have := h.trans_le List.length_le_length_insertIdx
  (v.insertIdx i a)[j] = v[j] := by
-- proof
  apply fin h h_ij


-- created on 2025-10-09
