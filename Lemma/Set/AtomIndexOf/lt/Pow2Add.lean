import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[atomIndexOf_lt](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  [DecidableEq X]
  {k k' : ℕ}
  {E : Fin k → Set X}
  {E' : Fin k' → Set X}
  {x : X} :
-- imply
  atomIndexOf E E' x < 2^(k+k') :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.atomIndexOf_lt E E' x


-- created on 2026-10-22
