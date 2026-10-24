import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open FinitelyAdditiveMeasure


/--
[FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B B': ConcreteSigmaAlgebra X}
  {μ: CountablyAdditiveMeasure B}
-- given
  (hBB': B' ≤ B) :
-- imply
  (μ.toFinitelyAdditiveMeasure.restrict_alg hBB').isCountablyAdditive :=
-- proof
  FinitelyAdditiveMeasure.isCountablyAdditive_restrict_alg μ hBB'


-- created on 2026-10-22
