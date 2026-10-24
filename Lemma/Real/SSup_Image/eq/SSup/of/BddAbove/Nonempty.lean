import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open EReal


/--
[EReal.sSup_image_coe](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {S : Set ℝ}
-- given
  (hne : S.Nonempty)
  (hbdd : BddAbove S) :
-- imply
  sSup ((fun x:ℝ ↦ (x:EReal)) '' S) = ((sSup S : ℝ) : EReal) :=
-- proof
  EReal.sSup_image_coe hne hbdd


-- created on 2026-10-22
