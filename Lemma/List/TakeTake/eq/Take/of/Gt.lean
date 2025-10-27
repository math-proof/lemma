import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (h : i > j) 
  (v : List α):
-- imply
  (v.take i).take j = v.take j := by
-- proof
  apply TakeTake.eq.Take.of.Ge
  omega


-- created on 2025-10-27
