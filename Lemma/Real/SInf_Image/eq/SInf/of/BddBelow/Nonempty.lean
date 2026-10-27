import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval
open EReal


/--
[EReal.sInf_image_coe](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {s : Set ℝ}
-- given
  (hs : s.Nonempty)
  (h_bdd : BddBelow s) :
-- imply
  sInf ((fun x : ℝ => (x : EReal)) '' s) = ↑(sInf s) :=
-- proof
  EReal.sInf_image_coe hs h_bdd


-- created on 2026-10-22
