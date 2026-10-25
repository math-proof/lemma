import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Continuous


/--
[Continuous.UnsignedMeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf: Continuous f)
  (hnonneg: Unsigned f) :
-- imply
  _root_.UnsignedMeasurable f :=
-- proof
  Continuous.UnsignedMeasurable hf hnonneg


-- created on 2026-10-22
