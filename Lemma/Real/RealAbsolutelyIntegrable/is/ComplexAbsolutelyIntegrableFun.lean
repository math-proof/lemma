import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ} :
-- imply
  RealAbsolutelyIntegrable f ↔ ComplexAbsolutelyIntegrable (fun x ↦ (f x:ℂ)) :=
-- proof
  RealAbsolutelyIntegrable.iff f


-- created on 2026-10-22
