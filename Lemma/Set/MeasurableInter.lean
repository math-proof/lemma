import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open ConcreteBooleanAlgebra


/--
[ConcreteBooleanAlgebra.inter_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {E F : Set X}
-- given
  (hE : B.measurable E)
  (hF : B.measurable F) :
-- imply
  B.measurable (E ∩ F) :=
-- proof
  ConcreteBooleanAlgebra.inter_mem B hE hF


-- created on 2026-10-22
