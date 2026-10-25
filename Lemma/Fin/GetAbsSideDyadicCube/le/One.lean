import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[sidelength_le_one](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d n : ℕ}
  {a: Fin d → ℤ}
  {i : Fin d} :
-- imply
  |(DyadicCube (n:ℤ) a).side i|ₗ ≤ 1 :=
-- proof
  DyadicCube.sidelength_le_one a i


-- created on 2026-10-22
