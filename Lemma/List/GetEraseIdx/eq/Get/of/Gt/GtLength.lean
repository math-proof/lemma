import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length > i)
  (h_j : i > j) :
-- imply
  let  := LengthEraseIdx.eq.SubLength_1.of.GtLength h_i
  (s.eraseIdx i)[j] = s[j] := by
-- proof
  grind


-- created on 2025-06-22
-- updated on 2025-11-26
