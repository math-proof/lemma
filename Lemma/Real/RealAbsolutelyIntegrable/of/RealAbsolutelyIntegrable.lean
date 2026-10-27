import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
  {c:ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f) :
-- imply
  RealAbsolutelyIntegrable (c • f) :=
-- proof
  RealAbsolutelyIntegrable.smul hf c


-- created on 2026-10-22
