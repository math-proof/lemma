import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Continuous


/--
[Continuous.RealMeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
-- given
  (hf: Continuous f) :
-- imply
  RealMeasurable f :=
-- proof
  Continuous.RealMeasurable hf


-- created on 2026-10-22
