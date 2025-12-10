import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Hyperreal.GeSqrt_0
import Lemma.Hyperreal.NeSqrt_0.of.Gt_0
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x > 0) :
-- imply
  √x > 0 := by
-- proof
  have := GeSqrt_0 x
  have h_Ne := NeSqrt_0.of.Gt_0 h
  exact Gt.of.Ge.Ne this h_Ne


-- created on 2025-12-10
