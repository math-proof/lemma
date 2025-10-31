import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (h : i > j)
  (s : List α):
-- imply
  (s.take i).take j = s.take j := by
-- proof
  apply TakeTake.eq.Take.of.Ge
  omega


-- created on 2025-10-27
