import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open EuclideanSpace'


/--
[EuclideanSpace'.isBounded_of_dim_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {E: Set (EuclideanSpace' 0)} :
-- imply
  Bornology.IsBounded E :=
-- proof
  EuclideanSpace'.isBounded_of_dim_zero E


-- created on 2026-10-22
