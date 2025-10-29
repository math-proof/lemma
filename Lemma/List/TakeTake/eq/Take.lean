import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.take i).take i = s.take i := by
-- proof
  apply TakeTake.eq.Take.of.Ge
  rfl


-- created on 2025-10-29
