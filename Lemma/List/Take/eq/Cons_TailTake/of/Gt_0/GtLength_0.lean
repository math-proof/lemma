import Lemma.List.Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0
open List


@[main]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > 0)
  (h_i : i > 0) :
-- imply
  s.take i = s[0] :: (s.take i).tail := by
-- proof
  rw [Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0 h h_i]
  congr 1


-- created on 2026-07-20
