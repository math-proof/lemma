import Lemma.List.DropTake.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  {v : List α}
-- given
  (i : Fin v.length) :
-- imply
  (v.take (i + 1)).drop i = [v[i]] := by
-- proof
  apply DropTake.eq.ListGet.of.Lt_Length


-- created on 2025-10-27
