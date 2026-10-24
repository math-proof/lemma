import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[mem_singleAtom_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {k : ℕ}
  {E : Fin k → Set X}
  {n : Fin (2^k)}
  {x : X} :
-- imply
  x ∈ singleAtom E n ↔ ∀ i : Fin k, n.val.testBit i.val ↔ x ∈ E i :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.mem_singleAtom_iff E n x


-- created on 2026-10-22
