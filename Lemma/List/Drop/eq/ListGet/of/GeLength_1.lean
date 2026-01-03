import Lemma.List.Drop.eq.ListGet.of.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ 1) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  apply Drop.eq.ListGet.of.GtLength_0
  omega


-- created on 2026-01-03
