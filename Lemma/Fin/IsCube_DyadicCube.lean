import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open DyadicCube


/--
[DyadicCube.isCube](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a: Fin d → ℤ} :
-- imply
  IsCube (DyadicCube n a) :=
-- proof
  DyadicCube.isCube n a


-- created on 2026-10-22
