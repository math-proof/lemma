import Lemma.Hyperreal.GeSt_0.of.Ge_0
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : st x < 0) :
-- imply
  x < 0 := by
-- proof
  if h : x < 0 then
    assumption
  else
    simp at h
    have := GeSt_0.of.Ge_0 h
    linarith


-- created on 2025-12-11
