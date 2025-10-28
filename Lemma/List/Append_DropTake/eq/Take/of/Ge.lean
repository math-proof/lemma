import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  
  (h : m ≥ n) 
  (s : List α):
-- imply
  s.take n ++ (s.take m).drop n = s.take m := by
-- proof
  rw [← TakeTake.eq.Take.of.Ge h]
  simp


-- created on 2025-10-28
