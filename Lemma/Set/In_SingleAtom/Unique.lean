import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[exists_unique_singleAtom](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  [DecidableEq X]
  {k : ℕ}
  {E : Fin k → Set X}
  {x : X} :
-- imply
  ∃! n : Fin (2^k), x ∈ singleAtom E n :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.exists_unique_singleAtom E x


-- created on 2026-10-22
