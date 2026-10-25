import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open EuclideanSpace'


/--
[EuclideanSpace'.uncountable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
-- given
  (hd: 0 < d) :
-- imply
  Uncountable (EuclideanSpace' d) :=
-- proof
  EuclideanSpace'.uncountable d hd


-- created on 2026-10-22
