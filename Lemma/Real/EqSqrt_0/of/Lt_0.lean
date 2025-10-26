import Lemma.Nat.Le.of.Lt
import Lemma.Real.EqSqrt_0.of.Le_0
open Nat Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  √x = 0 := by
-- proof
  have := Le.of.Lt h
  apply EqSqrt_0.of.Le_0 this


-- created on 2025-04-06
