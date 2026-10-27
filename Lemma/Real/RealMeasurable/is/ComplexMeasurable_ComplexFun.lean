import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open RealMeasurable


/--
[RealMeasurable.iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ} :
-- imply
  RealMeasurable f ↔ ComplexMeasurable (Real.complex_fun f) :=
-- proof
  RealMeasurable.iff


-- created on 2026-10-22
