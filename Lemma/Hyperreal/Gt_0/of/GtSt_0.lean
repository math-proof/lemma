import Lemma.Hyperreal.LeSt_0.of.Le_0
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : st x > 0) :
-- imply
  x > 0 := by
-- proof
  contrapose! h
  have := LeSt_0.of.Le_0 h
  linarith


-- created on 2025-12-11
