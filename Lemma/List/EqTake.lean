import Lemma.List.EqTake.of.Ge_Length
open List


@[main]
private lemma main
  -- given
  (s : List α) :
-- imply
  s.take s.length = s := by
-- proof
  apply EqTake.of.Ge_Length
  rfl


-- created on 2025-10-20
