import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.EqAppendTake__Drop
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ 2) :
-- imply
  s.take (s.length - 2) ++ [s[s.length - 2], s[s.length - 1]] = s := by
-- proof
  rw [ListGetS.eq.Drop.of.GeLength_2 h]
  rw [EqAppendTake__Drop]


-- created on 2026-07-04
