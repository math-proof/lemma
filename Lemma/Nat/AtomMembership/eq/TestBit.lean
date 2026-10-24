import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[atomMembership_eq_testBit](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {k k' n i : ℕ} :
-- imply
  atomMembership k k' n i = n.testBit i :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.atomMembership_eq_testBit k k' n i


-- created on 2026-10-22
