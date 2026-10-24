import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_eq_of_set_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F)
  (h: E = F) :
-- imply
  hE.measure = hF.measure :=
-- proof
  IsElementary.measure_eq_of_set_eq hE hF h


-- created on 2026-10-22
