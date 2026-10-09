import Lemma.List.EqRotate_Length
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : n = s.length) :
-- imply
  s.rotate n = s := by
-- proof
  subst h
  apply EqRotate_Length


-- created on 2025-10-19
