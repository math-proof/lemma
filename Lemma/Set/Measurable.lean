import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_4_3.Part5
open ConcreteBooleanAlgebra


/--
[ConcreteBooleanAlgebra.diff_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {E F : Set X}
-- given
  (hE : B.measurable E)
  (hF : B.measurable F) :
-- imply
  B.measurable (E \ F) :=
-- proof
  ConcreteBooleanAlgebra.diff_mem B hE hF


-- created on 2026-10-22
