import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open IsElementary


/--
[IsElementary.inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F) :
-- imply
  IsElementary (E ∩ F) :=
-- proof
  IsElementary.inter hE hF


-- created on 2026-10-22
