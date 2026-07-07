import Lemma.Hyperreal.GeSt_0.of.Ge_0
import Lemma.Hyperreal.StSub.eq.SubSt.of.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : ¬x → ∞)
  (h_r : x ≥ r) :
-- imply
  stdPart x ≥ r := by
-- proof
  suffices stdPart (x - r) ≥ 0 by
    rw [StSub.eq.SubSt.of.NotInfinite h] at this
    simpa
  apply GeSt_0.of.Ge_0
  simpa


-- created on 2025-12-21
