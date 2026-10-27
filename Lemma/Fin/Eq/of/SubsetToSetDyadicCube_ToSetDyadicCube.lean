import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[dyadicCubeNoProperContainmentSameScale](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a b : Fin d → ℤ}
-- given
  (h_sub : (DyadicCube n a).toSet ⊆ (DyadicCube n b).toSet) :
-- imply
  a = b :=
-- proof
  dyadicCubeNoProperContainmentSameScale h_sub


-- created on 2026-10-22
