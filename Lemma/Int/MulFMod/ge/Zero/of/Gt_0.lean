import Lemma.Int.FMod.ge.Zero.of.Gt_0
import Lemma.Algebra.GeMulS.of.Ge.Gt_0
import Lemma.Algebra.EqMul0_0
open Algebra Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n.fmod d * d ≥ 0 := by
-- proof
  have := FMod.ge.Zero.of.Gt_0 (n := n) h
  have := GeMulS.of.Ge.Gt_0 this h
  rwa [EqMul0_0] at this


-- created on 2025-03-23
