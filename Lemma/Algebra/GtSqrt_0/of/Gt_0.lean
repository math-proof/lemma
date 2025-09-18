import Lemma.Algebra.GeSqrt_0
import Lemma.Algebra.NeSqrt_0.of.Gt_0
import Lemma.Algebra.Gt.is.Ge.Ne
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  √x > 0 := by
-- proof
  have := GeSqrt_0 (x := x)
  have h_Ne := NeSqrt_0.of.Gt_0 h
  exact Gt.of.Ge.Ne this h_Ne


-- created on 2025-04-06
