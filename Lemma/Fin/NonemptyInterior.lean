import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[dyadicCubeInteriorNonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a: Fin d → ℤ} :
-- imply
  (interior (s := (DyadicCube n a).toSet)).Nonempty :=
-- proof
  dyadicCubeInteriorNonempty n a


-- created on 2026-10-22
