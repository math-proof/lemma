import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[atomIndexOf_testBit_E](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  [DecidableEq X]
  {k k' : ℕ}
  {E : Fin k → Set X}
  {E' : Fin k' → Set X}
  {x : X}
  {j : Fin k} :
-- imply
  (atomIndexOf E E' x).testBit j.val ↔ x ∈ E j :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.atomIndexOf_testBit_E E E' x j


-- created on 2026-10-22
