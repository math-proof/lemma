import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open FinitelyAdditiveMeasure


/--
[FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  (FinitelyAdditiveMeasure.lebesgue d).isCountablyAdditive :=
-- proof
  FinitelyAdditiveMeasure.lebesgue_isCountablyAdditive d


-- created on 2026-10-22
