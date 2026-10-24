import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open DyadicCube


/--
[pairwise_almost_disjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ} :
-- imply
  Pairwise (Function.onFun AlmostDisjoint (DyadicCube n : (Fin d → ℤ) → Box d)) :=
-- proof
  DyadicCube.pairwise_almost_disjoint n


-- created on 2026-10-22
