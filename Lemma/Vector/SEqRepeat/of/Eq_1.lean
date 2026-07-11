import Lemma.Vector.SEqRepeat_1
open Vector


@[main, cast]
private lemma main
-- given
  (h : d = 1)
  (x : List.Vector α n) :
-- imply
  x.repeat d ≃ x := by
-- proof
  subst h
  apply SEqRepeat_1


-- created on 2026-01-10
