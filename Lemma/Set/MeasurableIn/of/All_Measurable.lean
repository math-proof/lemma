import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Section_1_4_3.Part5
open ConcreteBooleanAlgebra


/--
[ConcreteBooleanAlgebra.finite_biUnion_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteBooleanAlgebra X}
  {I: Finset J}
  {E: J → Set X}
-- given
  (hE: ∀ j, B.measurable (E j)) :
-- imply
  B.measurable (⋃ j ∈ I, E j) :=
-- proof
  ConcreteBooleanAlgebra.finite_biUnion_mem B hE


-- created on 2026-10-22
