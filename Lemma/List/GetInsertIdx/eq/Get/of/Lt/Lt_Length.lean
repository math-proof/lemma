import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
open List


@[main]
private lemma fin
  {s : List α}
-- given
  (h : j < s.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  (s.insertIdx i a).get ⟨j, h.trans_le List.length_le_length_insertIdx⟩ = s.get ⟨j, h⟩ := by
-- proof
  apply List.get_insertIdx_of_lt
  assumption


@[main]
private lemma main
  {s : List α}
-- given
  (h : j < s.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  have := h.trans_le List.length_le_length_insertIdx
  (s.insertIdx i a)[j] = s[j] := by
-- proof
  apply fin h h_ij


-- created on 2025-10-09
