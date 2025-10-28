import Lemma.List.EqAppendTake__ListGet.of.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length = n + 1) :
-- imply
  s.take n ++ [s[n]] = s := by
-- proof
  have := EqAppendTake__ListGet.of.GtLength_0 (s := s) (by omega)
  simp_all


-- created on 2025-10-28
