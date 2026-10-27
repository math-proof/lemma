import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[atom_pairwiseDisjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {k k' : ℕ}
  {E : Fin k → Set X}
  {E' : Fin k' → Set X} :
-- imply
  Set.univ.PairwiseDisjoint (atom E E') :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.atom_pairwiseDisjoint E E'


-- created on 2026-10-22
