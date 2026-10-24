import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open UnsignedSimpleFunction.IntegralWellDef
open RealSimpleFunction.DisjointRepr


/--
[sum_indicator_eq_atomValue](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d k : ℕ}
  {c : Fin k → ℝ}
  {E : Fin k → Set (EuclideanSpace' d)}
  {n : Fin (2^k)}
  {x : EuclideanSpace' d}
-- given
  (hx : x ∈ singleAtom E n) :
-- imply
  (∑ i : Fin k, (c i) * (E i).indicator' x) = atomValue c n :=
-- proof
  RealSimpleFunction.DisjointRepr.sum_indicator_eq_atomValue c E n x hx


-- created on 2026-10-22
