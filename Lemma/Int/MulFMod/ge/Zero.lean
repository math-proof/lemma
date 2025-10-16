import Lemma.Int.MulFMod.ge.Zero.of.Gt_0
import Lemma.Int.MulFMod.ge.Zero.of.Lt_0
import Lemma.Algebra.Eq.of.NotLt.NotGt
open Algebra Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n.fmod d * d ≥ 0 := by
-- proof
  by_cases h : d > 0
  apply MulFMod.ge.Zero.of.Gt_0 h
  by_cases h' : d < 0
  apply MulFMod.ge.Zero.of.Lt_0 h'
  have := Eq.of.NotLt.NotGt h' h
  rw [this]
  simp


-- created on 2025-03-23
