import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.integral_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
  {k:ℕ}
  {c: Fin k → EReal}
  {E: Fin k → Set (EuclideanSpace' d)}
-- given
  (hf: UnsignedSimpleFunction f)
  (hmes: ∀ i, LebesgueMeasurable (E i))
  (hnonneg: ∀ i, c i ≥ 0)
  (heq: f = ∑ i, (c i) • (EReal.indicator (E i))) :
-- imply
  hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) :=
-- proof
  UnsignedSimpleFunction.integral_eq hf hmes hnonneg heq


-- created on 2026-10-22
