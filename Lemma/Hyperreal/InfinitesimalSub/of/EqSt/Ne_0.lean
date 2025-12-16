import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_r : r ≠ 0)
  (h_st : st x = r) :
-- imply
  Infinitesimal (x - r) := by
-- proof
  apply InfinitesimalSub.of.EqSt.NotInfinite _ h_st
  apply NotInfinite.of.NeSt_0
  aesop


-- created on 2025-12-16
