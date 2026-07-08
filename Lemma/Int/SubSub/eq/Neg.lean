import Lemma.Int.SubSub
open Int


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - a - b = -b := by
-- proof
  simp


@[main]
private lemma Comm
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - b - a = -b := by
-- proof
  rw [SubSub.comm]
  rw [main]


-- created on 2025-03-30
-- updated on 2026-07-08
