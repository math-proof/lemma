import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[set_eq_biUnion_atoms'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {k k' : ℕ}
  {E : Fin k → Set X}
  {E' : Fin k' → Set X}
  {i : Fin k'} :
-- imply
  E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.set_eq_biUnion_atoms' E E' i


-- created on 2026-10-22
