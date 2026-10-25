import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[nesting](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n m : ℤ}
  {a b : Fin d → ℤ} :
-- imply
  AlmostDisjoint (DyadicCube n a) (DyadicCube m b) ∨
      (DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet ∨
      (DyadicCube m b).toSet ⊆ (DyadicCube n a).toSet :=
-- proof
  DyadicCube.nesting


-- created on 2026-10-22
