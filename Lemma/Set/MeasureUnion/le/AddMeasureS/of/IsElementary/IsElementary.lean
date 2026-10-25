import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F) :
-- imply
  (hE.union hF).measure ≤ hE.measure + hF.measure :=
-- proof
  IsElementary.measure_of_union hE hF


-- created on 2026-10-22
