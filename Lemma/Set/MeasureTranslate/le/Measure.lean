import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open Pointwise
open JordanMeasurable


/--
[JordanMeasurable.measure_of_translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {x: EuclideanSpace' d}
-- given
  (hE: JordanMeasurable E) :
-- imply
  (hE.translate x).measure ≤ hE.measure :=
-- proof
  JordanMeasurable.measure_of_translate hE x


-- created on 2026-10-22
