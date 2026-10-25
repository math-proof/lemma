import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[singleAtom_pairwiseDisjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {k : ℕ}
  {E : Fin k → Set X} :
-- imply
  Set.univ.PairwiseDisjoint (singleAtom E) :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E


-- created on 2026-10-22
