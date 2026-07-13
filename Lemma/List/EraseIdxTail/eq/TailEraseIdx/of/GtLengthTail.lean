import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
open List


@[main]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h : i < s.tail.length) :
-- imply
  s.tail.eraseIdx i = (s.eraseIdx (i + 1)).tail := by
-- proof
  apply EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
  simp at h
  assumption


-- created on 2025-06-22
