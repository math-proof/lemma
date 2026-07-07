import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_r : r ≠ 0)
  (h_st : stdPart x = r) :
-- imply
  (x - r) → 0 := by
  apply InfinitesimalSub.of.EqSt.NotInfinite _ h_st
  intro h_inf
  have := EqSt_0.of.Infinite h_inf
  rw [h_st] at this
  exact h_r this


-- created on 2025-12-16
