import Lemma.List.DropTake.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  apply DropTake.eq.ListGet.of.Lt_Length


-- created on 2025-10-27
