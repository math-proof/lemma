import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[sidelength](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a: Fin d → ℤ}
  {i : Fin d} :
-- imply
  |(DyadicCube n a).side i|ₗ = (2:ℝ)^(-n) :=
-- proof
  DyadicCube.sidelength n a i


-- created on 2026-10-22
