import Lemma.List.LengthMap.eq.Length
open List


@[path]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  (s.map List.range).map List.length = s := by
-- proof
  ext i k
  simp_all


-- created on 2025-06-11
