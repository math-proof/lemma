import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[EuclideanSpace'_dist_eq_Real_dist](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {x y : EuclideanSpace' 1} :
-- imply
  dist x y = dist (EuclideanSpace'.equiv_Real x) (EuclideanSpace'.equiv_Real y) :=
-- proof
  EuclideanSpace'_dist_eq_Real_dist x y


-- created on 2026-10-22
