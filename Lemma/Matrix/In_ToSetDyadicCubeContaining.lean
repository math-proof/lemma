import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[dyadicCubeContaining_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {x : EuclideanSpace' d} :
-- imply
  x ∈ (dyadicCubeContaining n x).toSet :=
-- proof
  dyadicCubeContaining_mem n x


-- created on 2026-10-22
