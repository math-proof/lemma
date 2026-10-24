import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.measure_of_translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {x: EuclideanSpace' d}
-- given
  (hE: IsElementary E) :
-- imply
  (hE.translate x).measure = hE.measure :=
-- proof
  IsElementary.measure_of_translate hE x


-- created on 2026-10-22
