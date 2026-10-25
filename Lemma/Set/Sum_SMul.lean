import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open UnsignedSimpleFunction.IntegralWellDef
open RealSimpleFunction.DisjointRepr


/--
[eq_sum_atomValue_indicator](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d k : ℕ}
  {c : Fin k → ℝ}
  {E : Fin k → Set (EuclideanSpace' d)} :
-- imply
  (∑ i : Fin k, (c i) • (E i).indicator') = ∑ n : Fin (2^k), (atomValue c n) • (singleAtom E n).indicator' :=
-- proof
  RealSimpleFunction.DisjointRepr.eq_sum_atomValue_indicator c E


-- created on 2026-10-22
