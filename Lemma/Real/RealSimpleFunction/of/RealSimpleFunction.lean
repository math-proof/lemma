import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open RealSimpleFunction


/--
[RealSimpleFunction.smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
  {a: ℝ}
-- given
  (hf: RealSimpleFunction f) :
-- imply
  RealSimpleFunction (a • f) :=
-- proof
  RealSimpleFunction.smul hf a


-- created on 2026-10-22
