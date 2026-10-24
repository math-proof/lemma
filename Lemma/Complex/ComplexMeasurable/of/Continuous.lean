import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Continuous


/--
[Continuous.ComplexMeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
-- given
  (hf: Continuous f) :
-- imply
  ComplexMeasurable f :=
-- proof
  Continuous.ComplexMeasurable hf


-- created on 2026-10-22
