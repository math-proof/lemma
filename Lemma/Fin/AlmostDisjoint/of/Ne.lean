import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[almost_disjoint_same_scale](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a b : Fin d → ℤ}
-- given
  (hab : a ≠ b) :
-- imply
  AlmostDisjoint (DyadicCube n a) (DyadicCube n b) :=
-- proof
  DyadicCube.almost_disjoint_same_scale hab


-- created on 2026-10-22
