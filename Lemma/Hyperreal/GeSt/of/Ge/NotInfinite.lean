import Lemma.Hyperreal.GeSt_0.of.Ge_0
import Lemma.Hyperreal.StSub.eq.SubSt.of.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : ¬x.Infinite)
  (h_r : x ≥ r) :
-- imply
  x.st ≥ r := by
-- proof
  suffices (x - r).st ≥ 0 by 
    rw [StSub.eq.SubSt.of.NotInfinite h] at this
    simpa
  apply GeSt_0.of.Ge_0
  simpa


-- created on 2025-12-21
