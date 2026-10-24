import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[dyadicCubeLargerNotInSmaller](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n m : ℤ}
  {a b : Fin d → ℤ}
-- given
  (hd : 0 < d)
  (hnm : n < m) :
-- imply
  ¬((DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet) :=
-- proof
  dyadicCubeLargerNotInSmaller hd hnm


-- created on 2026-10-22
