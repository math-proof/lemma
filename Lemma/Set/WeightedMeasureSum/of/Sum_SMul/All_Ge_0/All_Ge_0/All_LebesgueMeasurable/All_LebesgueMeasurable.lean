import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[weightedMeasureSum_eq_of_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d k k' : ℕ}
  {c : Fin k → EReal}
  {E : Fin k → Set (EuclideanSpace' d)}
  {c' : Fin k' → EReal}
  {E' : Fin k' → Set (EuclideanSpace' d)}
-- given
  (hmes : ∀ i, LebesgueMeasurable (E i))
  (hmes' : ∀ i, LebesgueMeasurable (E' i))
  (hnonneg : ∀ i, c i ≥ 0)
  (hnonneg' : ∀ i, c' i ≥ 0)
  (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
-- imply
  weightedMeasureSum c E = weightedMeasureSum c' E' :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum_eq_of_eq hmes hmes' hnonneg hnonneg' heq


-- created on 2026-10-22
