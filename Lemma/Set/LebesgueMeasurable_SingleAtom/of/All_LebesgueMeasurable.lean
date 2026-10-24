import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open UnsignedSimpleFunction.IntegralWellDef
open RealSimpleFunction.DisjointRepr


/--
[singleAtom_measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d k : ℕ}
  {E : Fin k → Set (EuclideanSpace' d)}
  {n : Fin (2^k)}
-- given
  (hE : ∀ i, LebesgueMeasurable (E i)) :
-- imply
  LebesgueMeasurable (singleAtom E n) :=
-- proof
  RealSimpleFunction.DisjointRepr.singleAtom_measurable hE n


-- created on 2026-10-22
