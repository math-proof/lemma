import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendTake__Drop
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.dropLast ++ [s[s.length - 1]] = s := by
-- proof
  have := EqAppendTake__Drop s (s.length - 1)
  rw [Drop.eq.ListGet.of.GtLength_0 h] at this
  rwa [DropLast.eq.Take_SubLength_1]


-- created on 2025-11-24
