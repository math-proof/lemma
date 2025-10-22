import stdlib.List
import Lemma.List.Drop.eq.ListGet.of.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_n : n = s.length - 1) :
-- imply
  s.drop n = [s[n]] := by
-- proof
  subst h_n
  apply Drop.eq.ListGet.of.GtLength_0 h_s


-- created on 2025-10-22
