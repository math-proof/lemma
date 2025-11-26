import Lemma.List.EqTake.of.LeLength
open List


@[main]
private lemma main
  -- given
  (s : List α) :
-- imply
  s.take s.length = s := by
-- proof
  apply EqTake.of.LeLength
  rfl


-- created on 2025-10-20
