import Lemma.List.TakeCons.eq.Cons_Take.of.Gt_0
open List


@[main]
private lemma main
-- given
  (a : α)
  (b : List α) :
-- imply
  (a :: b).take (i + 1) = a :: b.take i := by
-- proof
  apply TakeCons.eq.Cons_Take.of.Gt_0
  grind


-- created on 2025-06-14
-- updated on 2026-07-22
