import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[cover_univ](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ} :
-- imply
  (⋃ (a : Fin d → ℤ), (DyadicCube n a).toSet) = Set.univ :=
-- proof
  DyadicCube.cover_univ n


-- created on 2026-10-22
