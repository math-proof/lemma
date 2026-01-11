import Lemma.Vector.Repeat_1.eq.Cast
open Vector


@[main]
private lemma main
-- given
  (h : d = 1)
  (x : List.Vector α n) :
-- imply
  x.repeat d = cast (by simp_all) x := by
-- proof
  subst h
  apply Repeat_1.eq.Cast


-- created on 2026-01-10
