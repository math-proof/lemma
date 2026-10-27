import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.abs_integ_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f) :
-- imply
  |hf.integ| ≤ hf.abs.integ :=
-- proof
  RealAbsolutelyIntegrable.abs_integ_le hf


-- created on 2026-10-22
