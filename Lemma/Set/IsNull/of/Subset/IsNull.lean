import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open IsNull


/--
[IsNull.subset](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F : Set (EuclideanSpace' d)}
-- given
  (hE : IsNull E)
  (hFE : F ⊆ E) :
-- imply
  IsNull F :=
-- proof
  IsNull.subset hE hFE


-- created on 2026-10-22
