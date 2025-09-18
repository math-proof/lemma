import Lemma.Algebra.FMod.ge.Zero.of.Gt_0
import Lemma.Algebra.GeMulS.of.Ge.Gt_0
import Lemma.Algebra.Mul0.eq.Zero
open Algebra


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
  rwa [Mul0.eq.Zero] at this


-- created on 2025-03-23
