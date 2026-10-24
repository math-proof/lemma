import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_2
open LebesgueMeasurable
open LebesgueMeasurable.boolean_algebra


/--
[LebesgueMeasurable.boolean_algebra.isSigmaAlgebra](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra :=
-- proof
  LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d


-- created on 2026-10-22
