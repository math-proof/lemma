import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[atom_measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d k k' : ℕ}
  {E : Fin k → Set (EuclideanSpace' d)}
  {E' : Fin k' → Set (EuclideanSpace' d)}
  {n : Fin (2^(k+k'))}
-- given
  (hE : ∀ i, LebesgueMeasurable (E i))
  (hE' : ∀ i, LebesgueMeasurable (E' i)) :
-- imply
  LebesgueMeasurable (atom E E' n) :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.atom_measurable hE hE' n


-- created on 2026-10-22
